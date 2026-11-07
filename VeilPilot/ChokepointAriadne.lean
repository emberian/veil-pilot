module
public import Veil

-- SMT answers are reconstructed as Lean proofs, not trusted
set_option veil.smt.trust false

/-! # Chokepoint device with Ariadne state continuity

Ariadne (Strackx and Piessens, USENIX Security 2016, §4.1, Listing 2;
`/Users/ember/paperbin/strackx2016-ariadne-state-continuity.txt`) keeps state continuity with one
monotonic counter `C` and MAC'd packages `(contents, ctr)` on untrusted disk:

* store:    write a package with `ctr = C + 1`, then increment `C`;
* retrieve: accept only a package with `ctr = C`; then, before resuming, twice
            (write a package with the recovered contents and `ctr = C + 1`, increment `C`).

The device state is the committed log (`log`); a frame is forwarded only after the increment that
commits it. Crashes may happen between any two steps. The adversary keeps every package ever
written (`used`; the MAC stops it forging) and may present any of them on restore, and may advance
the counter (denial of service only). The honest disk keeps the latest package per counter value
(`onDisk`), which is what Ariadne's `hdd.read(f, C)` returns.

The counter increment is one step: Ariadne stores `C` as a Gray code, so an increment is a single
bit flip (`VeilPilot/CounterWord.lean` shows why a binary word is not enough).

Variants (all `false` is Ariadne):
* `tolerateOne`  restore also accepts `ctr = C - 1` (the naive repair refuted in pilot 1);
* `singleInc`    retrieve increments once instead of twice (Ariadne's Appendix A.3 attack).
-/

veil module ChokepointAriadne

type frame
type pkgid
-- packages are allocated in order (removes the symmetric choice of a fresh id from the search)
instantiate pord : TotalOrder pkgid
open TotalOrder

param tolerateOne : Bool
param singleInc : Bool
param allowRollback : Bool
param allowAdvInc : Bool
param bound : Nat

enum mode = { boot, run, commit, down, rec1store, rec1inc, rec2store, rec2inc }

-- non-volatile counter (Gray-coded in hardware; one atomic step per increment here)
individual hw : Nat
individual pc : mode
individual halted : Bool
-- RAM
relation log (f : frame) : Bool
relation inflight (f : frame) : Bool
relation queued (f : frame) : Bool
-- packages: every package ever written (the adversary has them all), and the honest disk
relation used (p : pkgid) : Bool
function pkgCtr (p : pkgid) : Nat
relation pkgHas (p : pkgid) (f : frame) : Bool
relation onDisk (p : pkgid) : Bool
-- the world
relation forwarded (f : frame) : Bool
-- ghost: the counter value when the frame last left (for the proof, not for the device)
function fwdAt (f : frame) : Nat

#gen_state


-- Write a fresh package with counter `c` and the given contents; the honest disk keeps only the
-- latest package per counter value.
procedure writePkg (c : Nat) (g : frame) (withG : Bool) {
  let p :| ¬ used p ∧ ∀ q, ¬ used q → le p q
  used p := true
  pkgCtr p := c
  pkgHas p F := decide $ log F ∨ (withG ∧ F = g)
  onDisk P := decide $ onDisk P ∧ pkgCtr P ≠ c
  onDisk p := true
}

after_init {
  hw := 0
  pc := boot
  halted := false
  log F := false
  inflight F := false
  queued F := false
  used P := false
  pkgCtr P := 0
  pkgHas P F := false
  onDisk P := false
  forwarded F := false
  fwdAt F := 0
}

-- Ariadne's purge_state: the initial (empty) state is stored under counter 0
action purge (g : frame) {
  require pc = boot
  writePkg 0 g false
  pc := run
}

/-! ## Normal operation -/

action arrive (f : frame) {
  require pc = run ∧ ¬ halted
  writePkg (hw + 1) f true
  inflight f := true
  pc := commit
}

action commitInc {
  require pc = commit ∧ ¬ halted
  hw := hw + 1
  log F := decide $ log F ∨ inflight F
  queued F := decide $ queued F ∨ inflight F
  inflight F := false
  pc := run
}

action hostForward (f : frame) {
  require pc = run ∧ ¬ halted
  require queued f
  forwarded f := true
  fwdAt f := hw
  queued f := false
}

/-! ## Crash and Ariadne's retrieve -/

action crash {
  require pc ≠ down ∧ pc ≠ boot ∧ ¬ halted
  pc := down
  log F := false
  inflight F := false
  queued F := false
}

-- honest restore: the disk returns the package stored under the counter's value
action restore (p : pkgid) {
  require pc = down ∧ ¬ halted
  require onDisk p ∧ (pkgCtr p = hw ∨ (tolerateOne ∧ pkgCtr p + 1 = hw))
  log F := pkgHas p F
  pc := rec1store
}

-- honest restore finds nothing under the counter's value: fail-stop
action restoreMissing {
  require pc = down ∧ ¬ halted
  require ∀ p, ¬ (onDisk p ∧ (pkgCtr p = hw ∨ (tolerateOne ∧ pkgCtr p + 1 = hw)))
  halted := true
}

-- the adversary presents any package it kept; a stale one makes the device fail-stop
action restoreAdv (p : pkgid) {
  require allowRollback ∧ pc = down ∧ ¬ halted ∧ used p
  if pkgCtr p = hw ∨ (tolerateOne ∧ pkgCtr p + 1 = hw) then
    log F := pkgHas p F
    pc := rec1store
  else
    halted := true
}

action rec1Store (g : frame) {
  require pc = rec1store ∧ ¬ halted
  writePkg (hw + 1) g false
  pc := rec1inc
}

action rec1Inc {
  require pc = rec1inc ∧ ¬ halted
  hw := hw + 1
  if singleInc then
    pc := run
    queued F := log F
  else
    pc := rec2store
}

action rec2Store (g : frame) {
  require pc = rec2store ∧ ¬ halted
  writePkg (hw + 1) g false
  pc := rec2inc
}

action rec2Inc {
  require pc = rec2inc ∧ ¬ halted
  hw := hw + 1
  pc := run
  -- redrive: every committed frame goes back on the queue (downstream drops duplicates by id)
  queued F := log F
}

-- the adversary withholds every package: the device fail-stops
action failStop {
  require allowRollback ∧ pc = down ∧ ¬ halted
  halted := true
}

-- the adversary may advance the counter (denial of service; never a safety break)
action advInc {
  require allowAdvInc ∧ pc ≠ boot
  hw := hw + 1
}

-- Time passes with nothing to do. Without this step every infinite run of the bounded instance must
-- crash forever (crash is the only action left once packages or the counter bound run out), which
-- makes every "once crashes stop" property vacuous; the controls below caught that.
action idle {
  require pc ≠ boot
}

/-! ## Properties -/

-- Non-omission: while the device runs, every frame that has left is in its committed state.
-- Stated once for Ariadne's configuration and once for the variants, so that `#check_invariants`
-- never assumes an unproved clause for Ariadne (for Ariadne's parameters the variant clause is
-- vacuously true), and the model checker still reports the variants' violations.
safety [non_omission] (¬ tolerateOne ∧ ¬ singleInc) → pc = run ∧ ¬ halted ∧ forwarded F → log F
safety [non_omission_variants] (tolerateOne ∨ singleInc) → pc = run ∧ ¬ halted ∧ forwarded F → log F
-- No brick: with no adversary, the device never fail-stops.
safety [no_brick] (¬ allowRollback ∧ ¬ allowAdvInc) → ¬ halted


/-! ## The inductive invariant (Ariadne configuration) -/

ghost relation ariadne := ¬ tolerateOne ∧ ¬ singleInc

-- every package is at most one ahead of the counter
invariant [ahead_by_one] used P → pkgCtr P ≤ hw + 1
-- running, or between the increments of retrieve: no package is ahead of the counter
invariant [none_ahead] ariadne → (pc = run ∨ pc = rec2store) → used P → pkgCtr P ≤ hw
-- every package at or above the counter carries the committed state
invariant [fresh_has_log] ariadne → pc = run → used P ∧ pkgCtr P ≥ hw → log F → pkgHas P F
invariant [commit_fresh] ariadne → pc = commit → used P ∧ pkgCtr P ≥ hw → log F → pkgHas P F
invariant [commit_ahead] ariadne → pc = commit → used P ∧ pkgCtr P ≥ hw + 1 → (log F ∨ inflight F) → pkgHas P F
invariant [rec2_ahead] ariadne → pc = rec2inc → used P ∧ pkgCtr P ≥ hw + 1 → log F → pkgHas P F
-- a forwarded frame is in every package from its forwarding counter on, and in RAM while up
invariant [fwd_stamp] forwarded F → fwdAt F ≤ hw
invariant [fwd_in_later] ariadne → forwarded F ∧ used P ∧ pkgCtr P ≥ fwdAt F → pkgHas P F
invariant [fwd_in_ram] ariadne → forwarded F ∧ pc ≠ down → log F
-- with no adversary, the disk always holds a package under the counter's value
invariant [disk_fresh] (¬ allowRollback ∧ ¬ allowAdvInc) → pc ≠ boot → ∃ p, onDisk p ∧ pkgCtr p = hw
invariant [disk_next] (¬ allowRollback ∧ ¬ allowAdvInc) → (pc = commit ∨ pc = rec1inc ∨ pc = rec2inc) →
  ∃ p, onDisk p ∧ pkgCtr p = hw + 1
invariant [disk_used] onDisk P → used P
-- before purge: nothing written, nothing sent
invariant [boot_clean] pc = boot → ¬ used P ∧ hw = 0 ∧ ¬ forwarded F ∧ ¬ log F ∧ ¬ queued F
-- RAM queues
invariant [queued_logged] queued F → log F
invariant [down_empty] pc = down → ¬ queued F ∧ ¬ inflight F
invariant [inflight_commit] inflight F → pc = commit
invariant [rec_no_queue] (pc = rec1store ∨ pc = rec1inc ∨ pc = rec2store ∨ pc = rec2inc) → ¬ queued F

termination true

state_constraint [bounded] hw ≤ bound

-- The instance is bounded (counter ≤ bound, finitely many package ids), so a run can strand itself
-- at the bound; liveness is asked of runs that stay clear of it.
ghost relation room := hw + 3 ≤ bound ∧ ∃ p q r, p ≠ q ∧ q ≠ r ∧ p ≠ r ∧ ¬ used p ∧ ¬ used q ∧ ¬ used r

-- Liveness: with no adversary, once crashes stop, the device runs again. (An unapplied action in
-- `𝒲ℱ` means some instantiation of it; honest restore has one enabled package, and the two store
-- actions ignore their argument.)
temporal [recovers]
  𝒲ℱ restore ∧ 𝒲ℱ rec1Store ∧ 𝒲ℱ rec1Inc ∧
    𝒲ℱ rec2Store ∧ 𝒲ℱ rec2Inc ∧ 𝒲ℱ commitInc ∧ ◇ □ ¬ ⟨ crash ⟩ ∧ □ ⌜ room ⌝ →
    ◇ □ ⌜ ¬ halted ⌝ ∧ □ ◇ ⌜ pc = run ⌝

-- Liveness: with no adversary and strong fairness on forwarding, every committed frame leaves.
temporal [committed_forwarded]
  (∀ f, 𝒮ℱ (hostForward f)) ∧ 𝒲ℱ restore ∧ 𝒲ℱ rec1Store ∧ 𝒲ℱ rec1Inc ∧
    𝒲ℱ rec2Store ∧ 𝒲ℱ rec2Inc ∧ 𝒲ℱ commitInc ∧ ◇ □ ¬ ⟨ crash ⟩ ∧ □ ⌜ room ⌝ →
    ∀ f : frame, □ (⌜ pc = run ∧ log f ⌝ → ◇ ⌜ forwarded f ⌝)

-- Controls for the temporal checker (expected to FAIL): without fairness nothing need happen; and a
-- device that is down infinitely often is possible when crashes never stop.
temporal [ctrl_no_fairness] ◇ ⌜ pc = run ⌝ ∧ □ ◇ ⌜ pc = run ⌝
-- the antecedent of `recovers` with an impossible consequent: must FAIL unless the antecedent is
-- unsatisfiable on this system
temporal [ctrl_same_antecedent]
  𝒲ℱ restore ∧ 𝒲ℱ rec1Store ∧ 𝒲ℱ rec1Inc ∧
    𝒲ℱ rec2Store ∧ 𝒲ℱ rec2Inc ∧ 𝒲ℱ commitInc ∧ ◇ □ ¬ ⟨ crash ⟩ ∧ □ ⌜ room ⌝ →
    ◇ ⌜ halted ⌝
temporal [ctrl_c1] (◇ □ ¬ ⟨ crash ⟩) → ◇ ⌜ halted ⌝
temporal [ctrl_c2] (□ ¬ ⟨ crash ⟩) → ◇ ⌜ halted ⌝
temporal [ctrl_c3] (◇ □ ⌜ pc ≠ down ⌝) → ◇ ⌜ halted ⌝
temporal [ctrl_c4] 𝒲ℱ commitInc → ◇ ⌜ halted ⌝
temporal [ctrl_crashes_forever]
  𝒲ℱ restore ∧ 𝒲ℱ rec1Store ∧ 𝒲ℱ rec1Inc ∧ 𝒲ℱ rec2Store ∧ 𝒲ℱ rec2Inc ∧ 𝒲ℱ commitInc →
    ◇ □ ⌜ pc = run ⌝

#gen_spec

-- Every clause is checked for all instantiations (any frame and pkgid types, any parameters), with
-- the SMT answers reconstructed as Lean proofs. Only `non_omission_variants` fails (for
-- `commitInc`, `rec1Inc`, `rec2Inc`: the variants' attacks). Every other obligation passes, and for
-- Ariadne's parameters that failing clause is vacuous, so the induction closes there.
set_option veil.violationIsError false in
#check_invariants

/-! ## Runs (frame := Fin 2; sizes per run) -/

-- Ariadne, rollback adversary (Fin 5 packages, counter ≤ 3)
set_option veil.violationIsError false in
#model_check compiled { frame := Fin 2, pkgid := Fin 5, tolerateOne := false, singleInc := false, allowRollback := true, allowAdvInc := false, bound := 3 } {}

-- Ariadne, rollback and counter-advancing adversary (Fin 4 packages, counter ≤ 3)
set_option veil.violationIsError false in
#model_check compiled { frame := Fin 2, pkgid := Fin 4, tolerateOne := false, singleInc := false, allowRollback := true, allowAdvInc := true, bound := 3 } {}

-- Ariadne, honest disk, crashes only (Fin 7 packages, counter ≤ 5)
set_option veil.violationIsError false in
#model_check compiled { frame := Fin 2, pkgid := Fin 7, tolerateOne := false, singleInc := false, allowRollback := false, allowAdvInc := false, bound := 5 } {}
set_option veil.violationIsError false in
#temporal_check [recovers] compiled { frame := Fin 2, pkgid := Fin 7, tolerateOne := false, singleInc := false, allowRollback := false, allowAdvInc := false, bound := 5 } {} (route := .prune)
set_option veil.violationIsError false in
#temporal_check [committed_forwarded] compiled { frame := Fin 2, pkgid := Fin 7, tolerateOne := false, singleInc := false, allowRollback := false, allowAdvInc := false, bound := 5 } {} (route := .prune)
set_option veil.violationIsError false in
#temporal_check [ctrl_no_fairness] compiled { frame := Fin 2, pkgid := Fin 7, tolerateOne := false, singleInc := false, allowRollback := false, allowAdvInc := false, bound := 5 } {}
set_option veil.violationIsError false in
#temporal_check [ctrl_same_antecedent] compiled { frame := Fin 2, pkgid := Fin 7, tolerateOne := false, singleInc := false, allowRollback := false, allowAdvInc := false, bound := 5 } {} (route := .prune)
set_option veil.violationIsError false in
#temporal_check [ctrl_c1] compiled { frame := Fin 2, pkgid := Fin 7, tolerateOne := false, singleInc := false, allowRollback := false, allowAdvInc := false, bound := 5 } {}
set_option veil.violationIsError false in
#temporal_check [ctrl_c2] compiled { frame := Fin 2, pkgid := Fin 7, tolerateOne := false, singleInc := false, allowRollback := false, allowAdvInc := false, bound := 5 } {}
set_option veil.violationIsError false in
#temporal_check [ctrl_c3] compiled { frame := Fin 2, pkgid := Fin 7, tolerateOne := false, singleInc := false, allowRollback := false, allowAdvInc := false, bound := 5 } {}
set_option veil.violationIsError false in
#temporal_check [ctrl_c4] compiled { frame := Fin 2, pkgid := Fin 7, tolerateOne := false, singleInc := false, allowRollback := false, allowAdvInc := false, bound := 5 } {}
set_option veil.violationIsError false in
#temporal_check [ctrl_crashes_forever] compiled { frame := Fin 2, pkgid := Fin 7, tolerateOne := false, singleInc := false, allowRollback := false, allowAdvInc := false, bound := 5 } {}

-- naive repair: accept one behind, rollback adversary
set_option veil.violationIsError false in
#model_check compiled { frame := Fin 2, pkgid := Fin 4, tolerateOne := true, singleInc := false, allowRollback := true, allowAdvInc := false, bound := 3 } {}

-- Appendix A.3: one increment in retrieve, rollback adversary
set_option veil.violationIsError false in
#model_check compiled { frame := Fin 2, pkgid := Fin 6, tolerateOne := false, singleInc := true, allowRollback := true, allowAdvInc := false, bound := 3 } {}

end ChokepointAriadne
