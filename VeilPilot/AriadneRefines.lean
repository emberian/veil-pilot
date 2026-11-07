import VeilPilot.ChokepointAriadne
import AriadneStep

/-! # The Ariadne device refines the Veil model

`Chokepoint.Ariadne.wstep` (degg-research `experiments/chokepoint-step/AriadneStep.lean`: the
device step, every package it writes kept by the adversary, the bump adversary) is a forward
simulation of `ChokepointAriadne` (`VeilPilot/ChokepointAriadne.lean`) at Ariadne's parameters with
the rollback and counter-advancing adversary (`tolerateOne = singleInc = false`,
`allowRollback = allowAdvInc = true`), for every digest type, every hash and every bound:

* `init_corresponds`: the image of `world0` is one Veil step (`purge`) from Veil's initial state;
* `step_simulates`: every admissible device step from a reachable world maps to one Veil step
  between the images; device steps that change nothing map to Veil's `idle`;
* `refines`: hence the image of every reachable device world is reachable in Veil.

Frames are the device's entries; package ids are positions in the list of packages written (Veil
allocates the least unused id, which is the next position); the honest-disk relation `onDisk` is
the latest package per counter value.

Control: `singleInc_not_simulated`. The Appendix A.3 strawman (one increment in retrieve) takes a
step that no Veil transition matches, from a world the honest device reaches
(`singleInc_premise_reachable`).
-/

namespace AriadneRefines

open Chokepoint.Ariadne
open ChokepointAriadne

instance {D : Type} [Inhabited D] : Inhabited (Entry D) := ⟨⟨0, default, []⟩⟩

/-- The Veil model at Ariadne's parameters, rollback and counter-advancing adversary. -/
noncomputable abbrev Sys (D : Type) [DecidableEq D] [Inhabited D] (b : Nat) :=
  relationalTransitionSystem (Entry D) Nat false false true true b mode_IndT

abbrev St (D : Type) [DecidableEq D] (b : Nat) :=
  State (FieldAbstractType (Entry D) Nat false false true true b mode_IndT)

def modeOf : Mode → mode_IndT
  | .run => .run | .commit => .commit | .down => .down
  | .rec1 => .rec1store | .rec1i => .rec1inc | .rec2 => .rec2store | .rec2i => .rec2inc

variable {D : Type} [DecidableEq D] [Inhabited D] {b : Nat}

/-- The package at position `P` (Veil's unused ids read as the initial all-zero package). -/
def pk (made : List (Pkg D)) (P : Nat) : Pkg D := made.getD P ⟨0, []⟩

/-- The honest disk: the latest package written under its counter value. -/
def latest (made : List (Pkg D)) (P : Nat) : Bool :=
  decide (P < made.length ∧ ∀ j, j < made.length → P < j → (pk made j).ctr ≠ (pk made P).ctr)

/-- The counter when the entry last left (Veil's ghost `fwdAt`). -/
def lastAt (fwd : List (Entry D × Nat)) (F : Entry D) : Nat :=
  fwd.foldl (fun a p => if p.1 = F then p.2 else a) 0

/-- The abstraction: a device world as a Veil state. -/
def abs (w : World D) : St D b :=
  { hw := w.dev.hw, pc := modeOf w.dev.pc, halted := w.dev.halted,
    log := fun F => decide (F ∈ w.dev.log),
    inflight := fun F => decide (F ∈ w.dev.inflight),
    queued := fun F => decide (F ∈ w.dev.queue),
    used := fun P => decide (P < w.made.length),
    pkgCtr := fun P => (pk w.made P).ctr,
    pkgHas := fun P F => decide (F ∈ (pk w.made P).log),
    onDisk := latest w.made,
    forwarded := fun F => w.fwd.any (fun p => decide (p.1 = F)),
    fwdAt := lastAt w.fwd }


@[simp] theorem m_boot : (mode_EnumClass.boot : mode_IndT) = .boot := rfl
@[simp] theorem m_run : (mode_EnumClass.run : mode_IndT) = .run := rfl
@[simp] theorem m_commit : (mode_EnumClass.commit : mode_IndT) = .commit := rfl
@[simp] theorem m_down : (mode_EnumClass.down : mode_IndT) = .down := rfl
@[simp] theorem m_rec1store : (mode_EnumClass.rec1store : mode_IndT) = .rec1store := rfl
@[simp] theorem m_rec1inc : (mode_EnumClass.rec1inc : mode_IndT) = .rec1inc := rfl
@[simp] theorem m_rec2store : (mode_EnumClass.rec2store : mode_IndT) = .rec2store := rfl
@[simp] theorem m_rec2inc : (mode_EnumClass.rec2inc : mode_IndT) = .rec2inc := rfl

/-- Unfold one Veil transition to its guard and its successor state. -/
macro "veil_tr" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp [Sys, relationalTransitionSystem, Next, NextAct,
  purge.ext.derived_eq, purge.ext.tr, arrive.ext.derived_eq, arrive.ext.tr,
  commitInc.ext.derived_eq, commitInc.ext.tr, hostForward.ext.derived_eq, hostForward.ext.tr,
  crash.ext.derived_eq, crash.ext.tr, restore.ext.derived_eq, restore.ext.tr,
  restoreMissing.ext.derived_eq, restoreMissing.ext.tr, restoreAdv.ext.derived_eq, restoreAdv.ext.tr,
  rec1Store.ext.derived_eq, rec1Store.ext.tr, rec1Inc.ext.derived_eq, rec1Inc.ext.tr,
  rec2Store.ext.derived_eq, rec2Store.ext.tr, rec2Inc.ext.derived_eq, rec2Inc.ext.tr,
  failStop.ext.derived_eq, failStop.ext.tr, advInc.ext.derived_eq, advInc.ext.tr,
  idle.ext.derived_eq, idle.ext.tr, setIn, getFrom, Veil.FieldRepresentation.get,
  Veil.FieldRepresentation.setSingle, fieldRepresentationSetSimpPost, abs] $(loc)?)

set_option hygiene false in
/-- Split a package position into: before, the new package, after. -/
macro "pkg_cases" a:term:max made:term:max : tactic => `(tactic|
  (by_cases h1 : $a < List.length $made
   · simp [h1, Nat.ne_of_lt h1, (Nat.ne_of_lt h1).symm]
   · by_cases h2 : $a = List.length $made
     · simp [h2]
     · simp [h1, h2, Ne.symm h2, pk_ge (show List.length $made ≤ $a by omega)]))

theorem modeOf_ne_boot (m : Mode) : modeOf m ≠ .boot := by cases m <;> simp [modeOf]

/-! ## Lemmas about the abstraction -/

omit [DecidableEq D] [Inhabited D] in
theorem pk_snoc (made : List (Pkg D)) (q : Pkg D) (P : Nat) :
    pk (made ++ [q]) P =
      if P < made.length then pk made P else if P = made.length then q else ⟨0, []⟩ := by
  unfold pk
  by_cases h1 : P < made.length
  · simp [h1, List.getElem?_append_left h1]
  · by_cases h2 : P = made.length
    · subst h2; simp
    · have h3 : (made ++ [q]).length ≤ P := by simp; omega
      simp [h1, h2, List.getElem?_eq_none h3]

omit [DecidableEq D] [Inhabited D] in
theorem pk_ge {made : List (Pkg D)} {P : Nat} (h : made.length ≤ P) : pk made P = ⟨0, []⟩ := by
  simp [pk, List.getElem?_eq_none h]

omit [DecidableEq D] [Inhabited D] in
/-- Writing a package retires the older packages under its counter value. -/
theorem latest_snoc (made : List (Pkg D)) (q : Pkg D) (P : Nat) :
    latest (made ++ [q]) P = true ↔
      P = made.length ∨ (latest made P = true ∧ (pk made P).ctr ≠ q.ctr) := by
  simp only [latest, decide_eq_true_eq, List.length_append, List.length_singleton]
  constructor
  · rintro ⟨hP, hall⟩
    by_cases hl : P = made.length
    · exact Or.inl hl
    · have hlt : P < made.length := by omega
      refine Or.inr ⟨⟨hlt, fun j hj hPj => ?_⟩, ?_⟩
      · have := hall j (by omega) hPj
        simpa [pk_snoc, hj, hlt] using this
      · have := hall made.length (by omega) hlt
        simpa [pk_snoc, hlt, ne_comm] using this
  · rintro (hl | ⟨⟨hlt, hall⟩, hne⟩)
    · subst hl; exact ⟨by omega, fun j hj hPj => by omega⟩
    · refine ⟨by omega, fun j hj hPj => ?_⟩
      by_cases hjl : j < made.length
      · simpa [pk_snoc, hlt, hjl] using hall j hjl hPj
      · have hj' : j = made.length := by omega
        subst hj'; simpa [pk_snoc, hlt] using Ne.symm hne

omit [Inhabited D] in
theorem lastAt_append (fwd : List (Entry D × Nat)) (x : Entry D) (n : Nat) (F : Entry D) :
    lastAt (fwd ++ [(x, n)]) F = if x = F then n else lastAt fwd F := by
  simp [lastAt, List.foldl_append]

/-- A device step that changes nothing is Veil's `idle`. -/
theorem stutter {w w' : World D} (h : w' = w) : (Sys D b).next ⟨⟩ (abs w) (abs w') := by
  subst h
  exact ⟨.idle, by veil_tr; exact modeOf_ne_boot _⟩

/-- The adversary's counter bump is Veil's `advInc`. -/
theorem step_bump (H : List UInt8 → D) (w : World D) :
    (Sys D b).next ⟨⟩ (abs w) (abs (wstep H w .bump)) :=
  ⟨.advInc, by veil_tr; simp [wstep, modeOf_ne_boot]⟩

omit [DecidableEq D] [Inhabited D] in
theorem world_eta (w : World D) : ({ dev := w.dev, made := w.made ++ [], fwd := w.fwd ++ [] } : World D) = w := by
  cases w; simp

omit [Inhabited D] in
theorem step_halted (H : List UInt8 → D) (w : World D) (e : Event D) (hh : w.dev.halted = true) :
    wstep H w (.dev e) = w := by
  simp [wstep, step, hh, writesOf, forwardsOf]

theorem step_dev (H : List UInt8 → D) (w : World D) (e : Event D) (hI : Inv w)
    (ha : Admissible w (.dev e)) : (Sys D b).next ⟨⟩ (abs w) (abs (wstep H w (.dev e))) := by
  by_cases hh : w.dev.halted = true
  · exact stutter (step_halted H w e hh)
  have hh' : w.dev.halted = false := by simpa using hh
  cases e with
  | arrive p =>
    by_cases hpc : w.dev.pc = .run
    · refine ⟨.arrive ⟨w.dev.hw + 1, H p, p⟩, ?_⟩
      have hinf : w.dev.inflight = [] := hI.inflightOk (by simp [hpc])
      veil_tr
      simp only [wstep, step, hh', hpc, hinf]
      refine ⟨by simp [modeOf], trivial, w.made.length, Nat.le_refl _, fun q hq => hq, ?_⟩
      simp [modeOf, pk_snoc, writesOf, forwardsOf, eq_comm]
      refine ⟨fun a => ?_, fun a => ?_, fun x a => ?_, fun a => ?_⟩
      · by_cases h : a = w.made.length <;> simp [h] <;> omega
      · pkg_cases a w.made
      · pkg_cases a w.made
      · rw [Bool.eq_iff_iff, latest_snoc]
        by_cases h : a = w.made.length <;> simp [h]
    · exact stutter (by simp [wstep, step, hh', hpc, writesOf, forwardsOf])
  | tick =>
    cases hpc : w.dev.pc with
    | run => exact stutter (by simp [wstep, step, hh', hpc, writesOf, forwardsOf])
    | down => exact stutter (by simp [wstep, step, hh', hpc, writesOf, forwardsOf])
    | commit =>
      refine ⟨.commitInc, ?_⟩
      veil_tr
      simp only [wstep, step, hh', hpc]
      simp [modeOf, writesOf, forwardsOf]
    | rec1 =>
      refine ⟨.rec1Store default, ?_⟩
      veil_tr
      simp only [wstep, step, hh', hpc]
      simp [modeOf, pk_snoc, writesOf, forwardsOf, eq_comm]
      refine ⟨w.made.length, Nat.le_refl _, fun q hq => hq, fun a => ?_, fun a => ?_, fun x a => ?_, fun a => ?_⟩
      · by_cases h : a = w.made.length
        · simp [h]
        · simp [h, Ne.symm h]; omega
      · pkg_cases a w.made
      · pkg_cases a w.made
      · rw [Bool.eq_iff_iff, latest_snoc]
        by_cases h : a = w.made.length
        · simp [h]
        · simp [h, Ne.symm h]
    | rec1i =>
      refine ⟨.rec1Inc, ?_⟩
      veil_tr
      simp only [wstep, step, hh', hpc]
      simp [modeOf, writesOf, forwardsOf]
    | rec2 =>
      refine ⟨.rec2Store default, ?_⟩
      veil_tr
      simp only [wstep, step, hh', hpc]
      simp [modeOf, pk_snoc, writesOf, forwardsOf, eq_comm]
      refine ⟨w.made.length, Nat.le_refl _, fun q hq => hq, fun a => ?_, fun a => ?_, fun x a => ?_, fun a => ?_⟩
      · by_cases h : a = w.made.length
        · simp [h]
        · simp [h, Ne.symm h]; omega
      · pkg_cases a w.made
      · pkg_cases a w.made
      · rw [Bool.eq_iff_iff, latest_snoc]
        by_cases h : a = w.made.length
        · simp [h]
        · simp [h, Ne.symm h]
    | rec2i =>
      refine ⟨.rec2Inc, ?_⟩
      veil_tr
      simp only [wstep, step, hh', hpc]
      simp [modeOf, writesOf, forwardsOf]
  | forward =>
    by_cases hpc : w.dev.pc = .run
    · cases hq : w.dev.queue with
      | nil => exact stutter (by simp [wstep, step, hh', hpc, hq, writesOf, forwardsOf])
      | cons x rest =>
        refine ⟨.hostForward x, ?_⟩
        veil_tr
        simp only [wstep, step, hh', hpc, hq]
        simp [modeOf, writesOf, forwardsOf, lastAt_append]
        refine ⟨fun a => ?_, fun a => ?_⟩
        · by_cases h : a = x
          · subst h; simp
          · simp [h, Ne.symm h]
        · exact Bool.or_comm _ _
    · exact stutter (by simp [wstep, step, hh', hpc, writesOf, forwardsOf])
  | crash =>
    by_cases hpc : w.dev.pc = .down
    · exact stutter (by simp [wstep, step, hh', hpc, writesOf, forwardsOf])
    · refine ⟨.crash, ?_⟩
      veil_tr
      simp only [wstep, step, hh', hpc]
      simp [modeOf, writesOf, forwardsOf]
      cases hp : w.dev.pc <;> simp_all
  | restore q =>
    by_cases hpc : w.dev.pc = .down
    · cases q with
      | none =>
        refine ⟨.failStop, ?_⟩
        veil_tr
        simp only [wstep, step, hh', hpc]
        simp [modeOf, writesOf, forwardsOf]
      | some q =>
        obtain ⟨i, hi, hqi⟩ := List.mem_iff_getElem.mp (show q ∈ w.made from ha)
        have hpk : pk w.made i = q := by simp [pk, List.getElem?_eq_getElem hi, hqi]
        refine ⟨.restoreAdv i, ?_⟩
        veil_tr
        simp only [wstep, step, hh', hpc]
        simp [modeOf, hpk, hi]
        by_cases hc : q.ctr = w.dev.hw <;> simp [hc, writesOf, forwardsOf]
    · exact stutter (by cases q <;> simp [wstep, step, hh', hpc, writesOf, forwardsOf])

/-! ## The simulation -/

/-- Veil's initial state (`after_init`). -/
def veilInit : St D b :=
  { hw := 0, pc := .boot, halted := false, log := fun _ => false, inflight := fun _ => false,
    queued := fun _ => false, used := fun _ => false, pkgCtr := fun _ => 0,
    pkgHas := fun _ _ => false, onDisk := fun _ => false, forwarded := fun _ => false,
    fwdAt := fun _ => 0 }

/-- **init_corresponds.** The device's initial world is Veil's initial state after `purge`
(Ariadne's `purge_state`: the empty state stored under counter 0). -/
theorem init_corresponds :
    (Sys D b).assumptions ⟨⟩ ∧ (Sys D b).init ⟨⟩ veilInit ∧
      (Sys D b).next ⟨⟩ veilInit (abs (world0 : World D)) := by
  refine ⟨by simp [Sys, relationalTransitionSystem, Assumptions], ?_, .purge default, ?_⟩
  · simp [Sys, relationalTransitionSystem, Init, initializer.ext.tr, setIn, getFrom,
      Veil.FieldRepresentation.setSingle, fieldRepresentationSetSimpPost, veilInit]
  · veil_tr
    simp [veilInit, world0, modeOf, latest, pk, lastAt]
    refine ⟨0, fun q => Nat.zero_le q, fun a => eq_comm, fun a => ?_, fun x a => ?_, fun a => eq_comm⟩ <;>
      rcases a with _ | a <;> simp

/-- **step_simulates.** Every admissible step of the device from a reachable world is a Veil
transition between the images (steps that change nothing are Veil's `idle`). -/
theorem step_simulates (H : List UInt8 → D) {w : World D} {e : WEvent D} (hr : Reach H w)
    (ha : Admissible w e) : (Sys D b).next ⟨⟩ (abs w) (abs (wstep H w e)) := by
  cases e with
  | bump => exact step_bump H w
  | dev e => exact step_dev H w e (reach_inv hr) ha

/-- **refines.** The image of every reachable device world is a reachable Veil state. -/
theorem refines (H : List UInt8 → D) {w : World D} (hr : Reach H w) :
    (Sys D b).reachable ⟨⟩ (abs w) := by
  induction hr with
  | init =>
    obtain ⟨has, hinit, hnext⟩ := (init_corresponds : _ ∧ _ ∧ (Sys D b).next ⟨⟩ veilInit _)
    exact .step _ _ (.init _ has hinit) hnext
  | step hr ha ih => exact .step _ _ ih (step_simulates H hr ha)

/-! ## Control: one increment in retrieve does not refine -/

/-- **singleInc_not_simulated.** Ariadne's Appendix A.3 strawman resumes after one increment.
That step, from any running-retrieve world, is no Veil transition. -/
theorem singleInc_not_simulated (H : List UInt8 → D) (w : World D) (hpc : w.dev.pc = .rec1i)
    (hh : w.dev.halted = false) :
    ¬ (Sys D b).next ⟨⟩ (abs w) (abs (wstepWith (stepSingleInc H) w .tick)) := by
  rintro ⟨l, hl⟩
  cases l <;> veil_tr at hl <;> simp [wstepWith, stepSingleInc, hh, hpc, modeOf] at hl

omit [Inhabited D] in
/-- The control's premise is met: the honest device reaches the second step of retrieve. -/
theorem singleInc_premise_reachable (H : List UInt8 → D) :
    ∃ w : World D, Reach H w ∧ w.dev.pc = .rec1i ∧ w.dev.halted = false := by
  have r1 := Reach.step (e := .dev .crash) (Reach.init (H := H)) trivial
  have r2 := Reach.step (e := .dev (.restore (some ⟨0, []⟩))) r1 (by simp [Admissible, wstep, world0])
  have r3 := Reach.step (e := .dev .tick) r2 trivial
  exact ⟨_, r3, by simp [wstep, step, world0], by simp [wstep, step, world0]⟩

/-- info: 'AriadneRefines.refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms refines
/-- info: 'AriadneRefines.singleInc_not_simulated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms singleInc_not_simulated

end AriadneRefines
