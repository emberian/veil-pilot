module
public import Veil

set_option veil.deferVCGeneration true

/-! # Dark-learning custody handover under a mobile adversary

Our MPC fork holds the mind as additive SPDZ shares over n custodians (privacy until all n
collude) and has NO handover: `/Users/ember/dev/zkml-research/notes/dark-learning-handover-2721.md`
lists it as "none: a static committee". This is a design model of the obvious one, resharing:

* every old custodian `i` splits its share into subshares `sub i j` (summing to its share) and
  sends `sub i j` to new custodian `j`;
* new custodian `j` adds what it received (`Σ_i sub i j`) into its new share and drops the subshares;
* old custodian `i` erases its share (and the subshares it made) once all are sent.

Knowledge closure is three rounds of peeling over the row and column sums (sound: every derived fact
is derivable; not shown complete for general linear combinations, nor shown to reach the peeling
fixpoint in three rounds). So a violation is a real attack in the symbolic model, and "hidden" means
hidden from this closure, not from all linear algebra.

The adversary is mobile: it holds custodians period by period (see below), and a held custodian
leaks everything it currently holds. The properties call the secret leaked when the closure contains
every share of one sharing. Leakage is about shares only; values are not modelled (the standard symbolic abstraction).

Budget: at most `n - 1` distinct custodians may be corrupted within each period. `windowBoth`
chooses how the handover window counts: in BOTH periods (the proactive-secret-sharing rule) or only
in the new one. `senderErases` chooses whether a sender erases its subshares with its share, or
keeps them until the end of the handover.
-/

veil module CustodyHandover

type party
enum phase = { before, during, after }

param windowBoth : Bool
param senderErases : Bool
-- search-size switches: safety runs without crashes, liveness runs without the adversary
param allowCrash : Bool
param allowAdversary : Bool

individual ph : phase
-- protocol state
relation holdsOld (i : party) : Bool
relation holdsNew (j : party) : Bool
relation sent (i : party) (j : party) : Bool          -- sub i j has been delivered to j
relation senderKeeps (i : party) (j : party) : Bool   -- i still holds the sub i j it generated
relation combined (j : party) : Bool
relation gone (i : party) : Bool
relation crashed (i : party) : Bool
-- the adversary
relation corruptedOld (i : party) : Bool
relation corruptedNew (i : party) : Bool
relation kOld (i : party) : Bool
relation kNew (j : party) : Bool
relation kSub (i : party) (j : party) : Bool

#gen_state

after_init {
  ph := before
  holdsOld I := true
  holdsNew J := false
  sent I J := false
  senderKeeps I J := false
  combined J := false
  gone I := false
  crashed I := false
  corruptedOld I := false
  corruptedNew I := false
  kOld I := false
  kNew J := false
  kSub I J := false
}

/-! ## Adversary

Mobile, period by period: in each period it holds up to `n - 1` custodians and is evicted from them
when the period ends (periods are where proactive refresh puts the boundary). The old period ends
when the handover finishes (`windowBoth`) or when it starts (otherwise); the new period starts when
the handover starts. -/

ghost relation oldPeriod := ph = before ∨ (ph = during ∧ windowBoth)

/-! ## Leakage after every step, and the adversary's closure as ghost relations

Held parties leak continuously: `close` runs at the end of every action and records the raw facts.
Deductions are not state: the safety properties below read the peeling closure (`share_old i =
Σ_j sub i j`, `share_new j = Σ_i sub i j`: all terms give the sum; the sum and all but one term give
the last), unrolled three rounds as ghost relations. -/

procedure close {
  kOld I := decide $ kOld I ∨ (holdsOld I ∧ ((corruptedOld I ∧ oldPeriod) ∨ (corruptedNew I ∧ ph ≠ before)))
  kNew J := decide $ kNew J ∨ (holdsNew J ∧ ((corruptedOld J ∧ oldPeriod) ∨ (corruptedNew J ∧ ph ≠ before)))
  kSub I J := decide $ kSub I J ∨ (sent I J ∧ ¬ combined J ∧ ((corruptedOld J ∧ oldPeriod) ∨ (corruptedNew J ∧ ph ≠ before)))
    ∨ (senderKeeps I J ∧ ((corruptedOld I ∧ oldPeriod) ∨ (corruptedNew I ∧ ph ≠ before)))
}

ghost relation sub1 (i : party) (j : party) :=
  kSub i j ∨ (kOld i ∧ ∀ k, k ≠ j → kSub i k) ∨ (kNew j ∧ ∀ k, k ≠ i → kSub k j)
ghost relation old1 (i : party) := kOld i ∨ ∀ j, sub1 i j
ghost relation new1 (j : party) := kNew j ∨ ∀ i, sub1 i j
ghost relation sub2 (i : party) (j : party) :=
  sub1 i j ∨ (old1 i ∧ ∀ k, k ≠ j → sub1 i k) ∨ (new1 j ∧ ∀ k, k ≠ i → sub1 k j)
ghost relation old2 (i : party) := old1 i ∨ ∀ j, sub2 i j
ghost relation new2 (j : party) := new1 j ∨ ∀ i, sub2 i j
ghost relation sub3 (i : party) (j : party) :=
  sub2 i j ∨ (old2 i ∧ ∀ k, k ≠ j → sub2 i k) ∨ (new2 j ∧ ∀ k, k ≠ i → sub2 k j)
ghost relation old3 (i : party) := old2 i ∨ ∀ j, sub3 i j
ghost relation new3 (j : party) := new2 j ∨ ∀ i, sub3 i j

/-! ## Protocol -/

action startHandover {
  require ph = before
  ph := during
  -- with windowBoth, parties still held when the window opens are held inside it, so they count
  -- in the new period too (Codex astra review, 2026-11-06, item 5)
  if windowBoth then
    corruptedNew I := corruptedNew I ∨ corruptedOld I
  close
}

action send (i j : party) {
  require ph = during ∧ ¬ crashed i ∧ holdsOld i ∧ ¬ sent i j
  sent i j := true
  senderKeeps i j := true
  close
}

action combine (j : party) {
  require ph = during ∧ ¬ crashed j ∧ ¬ combined j
  require ∀ i, sent i j
  holdsNew j := true
  combined j := true
  close
}

action erase (i : party) {
  require ph = during ∧ ¬ crashed i ∧ holdsOld i
  require ∀ j, sent i j
  holdsOld i := false
  gone i := true
  if senderErases then
    senderKeeps i J := false
  close
}

action finish {
  require ph = during
  require ∀ i, gone i ∧ combined i
  ph := after
  senderKeeps I J := false
  close
}

action crash (i : party) {
  require allowCrash
  require ∀ k, ¬ crashed k     -- at most one crash
  crashed i := true
  close
}

action corruptOld (i : party) {
  require allowAdversary
  require oldPeriod ∧ ¬ corruptedOld i
  require ∃ k, k ≠ i ∧ ¬ corruptedOld k
  corruptedOld i := true
  -- with windowBoth, a corruption inside the window counts in both periods
  if ph = during then
    require corruptedNew i ∨ ∃ k, k ≠ i ∧ ¬ corruptedNew k
    corruptedNew i := true
  close
}

action corruptNew (i : party) {
  require allowAdversary
  require ph ≠ before ∧ ¬ corruptedNew i
  require ∃ k, k ≠ i ∧ ¬ corruptedNew k
  corruptedNew i := true
  if ph = during ∧ windowBoth then
    require corruptedOld i ∨ ∃ k, k ≠ i ∧ ¬ corruptedOld k
    corruptedOld i := true
  close
}

safety [old_secret_hidden] ¬ (∀ i, old3 i)
safety [new_secret_hidden] ¬ (∀ j, new3 j)
-- model sanity: an erasing sender holds no subshares (checks the bulk update takes effect)
invariant [sender_erases_effective] senderErases ∧ gone I → ¬ senderKeeps I J
-- Non-vacuity was checked once with `invariant [never_finishes] ph ≠ after` added here: it fails in
-- every adversary configuration (the shortest witness finishes without corrupting anyone;
-- runs/handover-nonvacuity.txt). The adversary is shown live by the windowBoth := false violation.

/-! Liveness: the handover completes if every protocol action is weakly fair. -/
temporal [completes]
  𝒲ℱ startHandover ∧ (∀ i, ∀ j, 𝒲ℱ (send i j)) ∧ (∀ j, 𝒲ℱ (combine j)) ∧ (∀ i, 𝒲ℱ (erase i)) ∧ 𝒲ℱ finish →
    ◇ ⌜ ph = after ⌝

#gen_spec

/-! ## Runs (party := Fin 3). Safety without crashes; liveness without the adversary. -/

-- windowBoth := true, senderErases := true
set_option veil.violationIsError false in
#model_check compiled { party := Fin 3, windowBoth := true, senderErases := true, allowCrash := false, allowAdversary := true } {}
-- windowBoth := false, senderErases := true
set_option veil.violationIsError false in
#model_check compiled { party := Fin 3, windowBoth := false, senderErases := true, allowCrash := false, allowAdversary := true } {}
-- windowBoth := true, senderErases := false
set_option veil.violationIsError false in
#model_check compiled { party := Fin 3, windowBoth := true, senderErases := false, allowCrash := false, allowAdversary := true } {}
set_option veil.violationIsError false in
#temporal_check [completes] compiled { party := Fin 3, windowBoth := true, senderErases := true, allowCrash := true, allowAdversary := false } {}
set_option veil.violationIsError false in
#temporal_check [completes] compiled { party := Fin 3, windowBoth := true, senderErases := true, allowCrash := false, allowAdversary := false } {}

end CustodyHandover
