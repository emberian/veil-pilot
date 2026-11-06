module
public import Veil

/-! # Chokepoint device, asynchronous host, crashes and rollback

Source: `/Users/ember/dev/degg-research/experiments/chokepoint-step/CommitStep.lean`.
That file proves `commit_before_forward` for a SYNCHRONOUS step: one transition persists the
leaf and forwards the frame. Its named residuals (README, and Astra S06 in
`research/governance-astra-response.md`) are that the host must execute `persist` before
`forward`, and that liveness carries fairness, store-progress and no-crash premises.

This model splits the step the way a real host executes it, and adds crash, restore and an
adversary that replays an older durable snapshot:

* `arrive f`      the device admits frame `f`: takes `occ := hw`, bumps the hardware counter
                   (TrInc, non-volatile), queues `persist` then `forward` (volatile).
* `hostPersist f` the durable append of the leaf; the durable counter becomes `occ f + 1`.
* `hostForward f` the frame leaves, only after its persist completed (the host obligation, a guard).
* `crash`         volatile state is lost (queued frames, the device's view).
* `restore`       CommitStep's rule: resume only if the durable counter equals `hw`, else halt.
* `saveSnapshot` / `rollback`   the adversary copies the durable store, later puts the copy back.

`counterAt` selects where the hardware counter advances: at admission (CommitStep's choice,
`counterAtPersist := false`) or at the durable commit (`true`, the alternative this pilot tests).
-/

veil module ChokepointAsync

type frame

param cap : Nat
param bound : Nat
param counterAtPersist : Bool
-- the host completes persists in occurrence order (a FIFO durable queue)
param inOrder : Bool
-- with counterAtPersist: the counter bump and the durable write are one atomic step (true), or two
-- (false: `bumpCounter` then `hostPersist`, with a crash possible in between)
param atomicCommit : Bool
-- the naive repair of a torn commit: restore also accepts a store exactly one behind the counter
param tolerateOne : Bool

-- non-volatile hardware counter (never decreases, survives crash and rollback)
individual hw : Nat
-- durable store: snapshot counter, log length, which frames have a durable leaf, and their ids
individual dCtr : Nat
individual dLen : Nat
relation persisted (f : frame) : Bool
function occOf (f : frame) : Nat
-- volatile device state
individual up : Bool
individual halted : Bool
individual ramLen : Nat
relation queued (f : frame) : Bool
relation bumped (f : frame) : Bool
-- the outside world: offered frames, forwarded frames (irreversible), refusals
relation offered (f : frame) : Bool
relation forwarded (f : frame) : Bool
relation refused (f : frame) : Bool
-- the adversary's copy of an earlier durable store
individual sCtr : Nat
individual sLen : Nat
relation sPersisted (f : frame) : Bool
individual sValid : Bool

#gen_state

after_init {
  hw := 0
  dCtr := 0
  dLen := 0
  persisted F := false
  occOf F := 0
  up := true
  halted := false
  ramLen := 0
  queued F := false
  bumped F := false
  offered F := true
  forwarded F := false
  refused F := false
  sCtr := 0
  sLen := 0
  sPersisted F := false
  sValid := false
}

action arrive (f : frame) {
  require up ∧ ¬ halted
  require offered f
  offered f := false
  if ramLen < cap then
    occOf f := hw
    queued f := true
    ramLen := ramLen + 1
    if ¬ counterAtPersist then
      hw := hw + 1
  else
    refused f := true
    if ¬ counterAtPersist then
      hw := hw + 1
}

action hostPersist (f : frame) {
  require up ∧ ¬ halted
  require queued f ∧ ¬ persisted f
  require inOrder → ∀ g, queued g ∧ occOf g < occOf f → persisted g
  require (counterAtPersist ∧ ¬ atomicCommit) → bumped f
  if counterAtPersist ∧ atomicCommit then
    -- the id is the counter value at the durable commit
    occOf f := hw
    hw := hw + 1
  persisted f := true
  dLen := dLen + 1
  dCtr := occOf f + 1
}

action bumpCounter (f : frame) {
  require counterAtPersist ∧ ¬ atomicCommit
  require up ∧ ¬ halted
  require queued f ∧ ¬ persisted f ∧ ¬ bumped f
  require ∀ g, ¬ (bumped g ∧ ¬ persisted g)
  occOf f := hw
  hw := hw + 1
  bumped f := true
}

action hostForward (f : frame) {
  require up ∧ ¬ halted
  require queued f ∧ persisted f ∧ ¬ forwarded f
  forwarded f := true
  queued f := false
}

action crash {
  require up
  up := false
  queued F := false
  bumped F := false
  -- a frame admitted but not yet persisted is lost with the RAM; its offer is gone too
}

action restore {
  require ¬ up
  up := true
  ramLen := dLen
  if dCtr = hw ∨ (tolerateOne ∧ dCtr + 1 = hw) then
    halted := false
    -- redrive: persisted frames go back on the forward queue (downstream dedups by occurrence id)
    queued F := persisted F ∧ ¬ forwarded F
  else
    halted := true
}

action saveSnapshot {
  sCtr := dCtr
  sLen := dLen
  sPersisted F := persisted F
  sValid := true
}

action rollback {
  require ¬ up ∧ sValid
  dCtr := sCtr
  dLen := sLen
  persisted F := sPersisted F
}

-- keeps the instance finite
state_constraint [bounded] hw ≤ bound

-- Non-omission at the effect level: while the device runs, every frame that has left it has a
-- durable leaf in the store it is running on.
safety [commit_before_forward] up ∧ ¬ halted ∧ forwarded F → persisted F
-- Forwarded ids are distinct across crashes and restores.
safety [forwarded_ids_distinct] forwarded F ∧ forwarded G ∧ occOf F = occOf G → F = G

termination true

/-! Liveness. Fairness on the host and on restore; crashes are allowed unless excluded. -/

-- Every admitted frame is eventually forwarded (with crashes allowed): expected to FAIL.
temporal [admitted_forwarded]
  (∀ f, 𝒲ℱ (bumpCounter f)) ∧ (∀ f, 𝒲ℱ (hostPersist f)) ∧ (∀ f, 𝒲ℱ (hostForward f)) ∧ 𝒲ℱ restore →
    ∀ f : frame, □ (⌜ queued f ⌝ → ◇ ⌜ forwarded f ⌝)

-- A frame whose leaf is durable is eventually forwarded, crashes allowed (honest: no rollback).
-- Weak fairness is not enough: a crash after every restore keeps `hostForward` from being
-- continuously enabled (found by the checker), so forwarding is strongly fair here.
temporal [persisted_forwarded]
  (∀ f, 𝒮ℱ (hostForward f)) ∧ 𝒲ℱ restore ∧ □ ¬ ⟨ rollback ⟩ →
    ∀ f : frame, □ (⌜ persisted f ⌝ → ◇ ⌜ forwarded f ⌝)

-- The same without crashes and without the adversary: expected to hold.
temporal [admitted_forwarded_nocrash]
  (∀ f, 𝒲ℱ (bumpCounter f)) ∧ (∀ f, 𝒲ℱ (hostPersist f)) ∧ (∀ f, 𝒲ℱ (hostForward f)) ∧ □ ¬ ⟨ crash ⟩ ∧ □ ¬ ⟨ rollback ⟩ →
    ∀ f : frame, □ (⌜ queued f ⌝ → ◇ ⌜ forwarded f ⌝)

-- An honest crash (no rollback) is always recovered from: the device does not stay halted.
temporal [honest_crash_recovers]
  𝒲ℱ restore ∧ □ ¬ ⟨ rollback ⟩ → □ ◇ ⌜ up ∧ ¬ halted ⌝

#gen_spec

/-! ## Runs (frame := Fin 2, capacity 2, hw ≤ 4). Each line is one configuration. -/

-- counterAtPersist := false, inOrder := false
set_option veil.violationIsError false in
#model_check interpreted { frame := Fin 2, cap := 2, bound := 4, counterAtPersist := false, inOrder := false, atomicCommit := true, tolerateOne := false } {}
set_option veil.violationIsError false in
#temporal_check [admitted_forwarded] interpreted { frame := Fin 2, cap := 2, bound := 4, counterAtPersist := false, inOrder := false, atomicCommit := true, tolerateOne := false } {}
set_option veil.violationIsError false in
#temporal_check [admitted_forwarded_nocrash] interpreted { frame := Fin 2, cap := 2, bound := 4, counterAtPersist := false, inOrder := false, atomicCommit := true, tolerateOne := false } {}
set_option veil.violationIsError false in
#temporal_check [persisted_forwarded] interpreted { frame := Fin 2, cap := 2, bound := 4, counterAtPersist := false, inOrder := false, atomicCommit := true, tolerateOne := false } {}
set_option veil.violationIsError false in
#temporal_check [honest_crash_recovers] interpreted { frame := Fin 2, cap := 2, bound := 4, counterAtPersist := false, inOrder := false, atomicCommit := true, tolerateOne := false } {}

-- counterAtPersist := false, inOrder := true
set_option veil.violationIsError false in
#model_check interpreted { frame := Fin 2, cap := 2, bound := 4, counterAtPersist := false, inOrder := true, atomicCommit := true, tolerateOne := false } {}
set_option veil.violationIsError false in
#temporal_check [admitted_forwarded] interpreted { frame := Fin 2, cap := 2, bound := 4, counterAtPersist := false, inOrder := true, atomicCommit := true, tolerateOne := false } {}
set_option veil.violationIsError false in
#temporal_check [admitted_forwarded_nocrash] interpreted { frame := Fin 2, cap := 2, bound := 4, counterAtPersist := false, inOrder := true, atomicCommit := true, tolerateOne := false } {}
set_option veil.violationIsError false in
#temporal_check [persisted_forwarded] interpreted { frame := Fin 2, cap := 2, bound := 4, counterAtPersist := false, inOrder := true, atomicCommit := true, tolerateOne := false } {}
set_option veil.violationIsError false in
#temporal_check [honest_crash_recovers] interpreted { frame := Fin 2, cap := 2, bound := 4, counterAtPersist := false, inOrder := true, atomicCommit := true, tolerateOne := false } {}

-- counterAtPersist := true, inOrder := false
set_option veil.violationIsError false in
#model_check interpreted { frame := Fin 2, cap := 2, bound := 4, counterAtPersist := true, inOrder := false, atomicCommit := true, tolerateOne := false } {}
set_option veil.violationIsError false in
#temporal_check [admitted_forwarded] interpreted { frame := Fin 2, cap := 2, bound := 4, counterAtPersist := true, inOrder := false, atomicCommit := true, tolerateOne := false } {}
set_option veil.violationIsError false in
#temporal_check [admitted_forwarded_nocrash] interpreted { frame := Fin 2, cap := 2, bound := 4, counterAtPersist := true, inOrder := false, atomicCommit := true, tolerateOne := false } {}
set_option veil.violationIsError false in
#temporal_check [persisted_forwarded] interpreted { frame := Fin 2, cap := 2, bound := 4, counterAtPersist := true, inOrder := false, atomicCommit := true, tolerateOne := false } {}
set_option veil.violationIsError false in
#temporal_check [honest_crash_recovers] interpreted { frame := Fin 2, cap := 2, bound := 4, counterAtPersist := true, inOrder := false, atomicCommit := true, tolerateOne := false } {}

-- counterAtPersist := true, atomicCommit := false (counter bump, then the durable write)
set_option veil.violationIsError false in
#model_check interpreted { frame := Fin 2, cap := 2, bound := 4, counterAtPersist := true, inOrder := false, atomicCommit := false, tolerateOne := false } {}
set_option veil.violationIsError false in
#temporal_check [admitted_forwarded_nocrash] interpreted { frame := Fin 2, cap := 2, bound := 4, counterAtPersist := true, inOrder := false, atomicCommit := false, tolerateOne := false } {}
set_option veil.violationIsError false in
#temporal_check [persisted_forwarded] interpreted { frame := Fin 2, cap := 2, bound := 4, counterAtPersist := true, inOrder := false, atomicCommit := false, tolerateOne := false } {}
set_option veil.violationIsError false in
#temporal_check [honest_crash_recovers] interpreted { frame := Fin 2, cap := 2, bound := 4, counterAtPersist := true, inOrder := false, atomicCommit := false, tolerateOne := false } {}

-- the torn-commit variant with the naive repair (restore accepts one behind)
set_option veil.violationIsError false in
#model_check interpreted { frame := Fin 2, cap := 2, bound := 4, counterAtPersist := true, inOrder := false, atomicCommit := false, tolerateOne := true } {}
set_option veil.violationIsError false in
#temporal_check [honest_crash_recovers] interpreted { frame := Fin 2, cap := 2, bound := 4, counterAtPersist := true, inOrder := false, atomicCommit := false, tolerateOne := true } {}

end ChokepointAsync
