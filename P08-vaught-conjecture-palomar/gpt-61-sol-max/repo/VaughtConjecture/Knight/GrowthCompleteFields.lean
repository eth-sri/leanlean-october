
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.RelativeLift
import VaughtConjecture.Knight.FullScopeZeroExtension

/-! # Complete growth fields and the active private fibre

The activation cutoff is the existing request grade, not an extra scalar gate.
Future private values remain stored literally. Zero tails are used only inside
the whole-private relative lift; they are not the returned complete vector.
The donor is already wholly present at activation. No physical carrier is built.
-/

namespace VaughtConjecture.Knight.Growth
section
variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}

structure State (DA : CellScheme A) (DQ : CellScheme Q) where
  privateValues : CellLabels DA
  donorValues : CellLabels DQ

abbrev Field (DA : CellScheme A) (DQ : CellScheme Q) := Cell DA ⊕ Cell DQ

local notation "State₀" => State DA DQ

namespace State
def profile (S : State₀) : Field DA DQ → ExtOrd :=
  Sum.elim S.privateValues S.donorValues

/-- Recover both complete vectors, including fields above the current cutoff. -/
def ofProfile (a : Field DA DQ → ExtOrd) : State₀ :=
  ⟨fun d => a (.inl d), fun d => a (.inr d)⟩

@[simp] theorem ofProfile_profile (S : State₀) : ofProfile S.profile = S := rfl

@[simp] theorem profile_ofProfile (a : Field DA DQ → ExtOrd) :
    (ofProfile a).profile = a := by
  funext f
  cases f <;> rfl

theorem profile_injective : Function.Injective (profile (DA := DA) (DQ := DQ)) := by
  intro S T h
  simpa only [ofProfile_profile] using congrArg ofProfile h

def map (σ : LabelMap) (S : State₀) : State₀ :=
  ⟨σ ∘ S.privateValues, σ ∘ S.donorValues⟩

theorem profile_map σ (S : State₀) f :
    (S.map σ).profile f = σ (S.profile f) := by cases f <;> rfl

def CapEq γ (S T : State₀) :=
  ∀ f, min (T.profile f) γ = min (S.profile f) γ

end State

variable (X : RelativeData DA semA DQ semQ)

/-- Complete root agreement is retained independently of relation activation.
The private and donor vectors include all future occurrences. -/
structure Admitted (j : ℕ) (S : State₀) : Prop where
  private_lawful : RespectsSemanticsBelow semA (A, j) (fun d => S.privateValues d.1)
  donor_lawful : RespectsSemanticsBelow semQ (Q, j) (fun d => S.donorValues d.1)
  visible : ∀ f, SelfVis 1 (S.profile f)
  shared : ∀ d , S.donorValues d.1 = S.privateValues (X.κ d).1
  correct : X.req.N ≤ j → InClass X.ZA S.privateValues →
    X.req.Correct (X.req.sec S.privateValues) S.donorValues

theorem Admitted.down {i j : ℕ} {S : State₀} (hS : Admitted X j S) (hij : i ≤ j) :
    Admitted X i S where
  private_lawful := RespectsSemanticsBelow.mono
    (CI := (A, i)) (BJ := (A, j)) ⟨Finset.Subset.refl _, hij⟩ hS.private_lawful
  donor_lawful := RespectsSemanticsBelow.mono
    (CI := (Q, i)) (BJ := (Q, j)) ⟨Finset.Subset.refl _, hij⟩ hS.donor_lawful
  visible := hS.visible
  shared := hS.shared
  correct hN := hS.correct (hN.trans hij)

def zero : State₀ := ⟨fun _ => ⊥, fun _ => ⊥⟩

theorem zero_admitted {j : ℕ} : Admitted X j (zero (DA := DA) (DQ := DQ)) where
  private_lawful := (RespectsSemanticsBelow.bot _ _)
  donor_lawful := (RespectsSemanticsBelow.bot _ _)
  visible f := by cases f <;> exact selfVis_bot
  shared _ := rfl
  correct _ hc := (X.C_notin ((hc X.req.capCell).mp rfl)).elim

local notation "below₀" => DA.belowCell X.req.C

def capAt {j} (hj : X.req.N ≤ j) (d : below₀) :
    DA.below (A, j) :=
  ⟨d.1, DA.scope_subset d.1,
    d.2.2.trans (X.grade_C.le.trans hj)⟩

theorem zeroAbove_cap {j} (hj : X.req.N ≤ j)
    p (d : below₀) :
    CellScheme.zeroAbove p d.1 = p (capAt X hj d) :=
  CellScheme.zeroAbove_low p (capAt X hj d)

theorem zeroAbove_capEq {j : ℕ} {p q : BelowLabels DA (A, j)} {γ : ExtOrd}
    (h : CappedEq p q γ) (d : Cell DA) :
    min (CellScheme.zeroAbove p d) γ = min (CellScheme.zeroAbove q d) γ := by simp_all [VaughtConjecture.Knight.CellScheme.zeroAbove] <;> aesop

/-- Restore the future bookkeeping coordinates after the temporary zero tail. -/
def complete {j : ℕ} (u : CellLabels DA) (p : BelowLabels DA (A, j))
    (d : Cell DA) :=
  if hd : DA.grade d ≤ j then
    p ⟨d, DA.scope_subset d, hd⟩ else u d

theorem complete_present {j} u
    p (d : DA.below (A, j)) : complete u p d.1 = p d := by
  have hd : DA.grade d.1 ≤ j := d.2.2
  rw [complete, dite_eq_left hd]
  rfl

theorem complete_future {j : ℕ} (u : CellLabels DA)
    (p : BelowLabels DA (A, j)) (d : Cell DA) (hd : j < DA.grade d) :
    complete u p d = u d := by rw [complete, dite_eq_right (not_le.mpr hd)]

/-- All-cap active private repair on the actual full-scope grade cutoff.
Neither the replacement donor nor its correctness is an input. Future private
fields, and every complete-field original cap, are retained. -/
theorem private_repair {j : ℕ} (hj : X.req.N ≤ j) {S : State₀}
    (hS : Admitted X j S) {p : BelowLabels DA (A, j)}
    (hp : RespectsSemanticsBelow semA (A, j) p) {γ : ExtOrd} (hγ : SelfVis j γ)
    (hag : ∀ d, min (p d) γ = min (S.privateValues d.1) γ) :
    ∃ T , Admitted X j T ∧
      (∀ d , T.privateValues d.1 = p d) ∧ S.CapEq γ T ∧
      ∀ d, j < DA.grade d → T.privateValues d = S.privateValues d := by
  let u₀ := CellScheme.zeroAbove (fun d : DA.below (A, j) => S.privateValues d.1)
  have hsec : X.req.sec u₀ = X.req.sec S.privateValues :=
    funext (fun d => zeroAbove_cap X hj
      (fun d => S.privateValues d.1) d)
  have hcls : InClass X.ZA u₀ ↔ InClass X.ZA S.privateValues := by
    unfold InClass
    simp only [show ∀ d , u₀ d.1 = S.privateValues d.1
      from fun d => zeroAbove_cap X hj _ d]
  have hv  := hS.donor_lawful.toRespects (fun d =>
      ⟨DQ.scope_subset d, (X.grade_le d).trans hj⟩)
  have hall : X.Allowed u₀ S.donorValues :=
    ⟨hS.private_lawful.zeroAbove, hv,
      fun d => (hS.shared d).trans (zeroAbove_cap X hj
        (fun d => S.privateValues d.1) (X.κ d)).symm,
      fun hc => hsec.symm ▸ hS.correct hj (hcls.mp hc)⟩
  obtain ⟨v, hv, hvcap⟩ := X.relative_lift hall hp.zeroAbove (hγ.mono hj)
    (zeroAbove_capEq hag)
  let T : State₀ := ⟨complete S.privateValues p, v⟩
  have hcapread (d : below₀) :
      T.privateValues d.1 = CellScheme.zeroAbove p d.1 :=
    (complete_present S.privateValues p (capAt X hj d)).trans (zeroAbove_cap X hj p d).symm
  refine ⟨T, ?_, complete_present S.privateValues p, ?_, complete_future S.privateValues p⟩
  · refine ⟨?_, hv.2.1.toBelow _, ?_, ?_, ?_⟩
    · aesop (add simp [complete_present])
    · intro f
      cases f with
      | inl d =>
        by_cases hd : DA.grade d ≤ j
        · have hpv : SelfVis (DA.grade d)
              (p ⟨d, DA.scope_subset d, hd⟩) :=
            (hp.orderly ⟨d, DA.scope_subset d, hd⟩).symm
          change SelfVis 1 (complete S.privateValues p d)
          rw [complete_present S.privateValues p
            ⟨d, DA.scope_subset d, hd⟩]
          exact hpv.mono (DA.grade_pos d)
        · rw [show T.profile (.inl d) = S.profile (.inl d) from
            complete_future S.privateValues p d (not_le.mp hd)]
          exact hS.visible _
      | inr d =>
        have hd : SelfVis (DQ.grade d) (v d) := (hv.2.1.orderly d).symm
        exact hd.mono (DQ.grade_pos d)
    · intro d
      exact (hv.2.2.1 d).trans (hcapread (X.κ d)).symm
    · intro _ hc
      have hc' : InClass X.ZA (CellScheme.zeroAbove p) := by
        intro d
        rw [← hcapread d]
        exact hc d
      exact (funext hcapread : X.req.sec T.privateValues =
        X.req.sec (CellScheme.zeroAbove p)).symm ▸ hv.2.2.2 hc'
  · intro f
    cases f with
    | inl d =>
      by_cases hd : DA.grade d ≤ j
      · change min (complete S.privateValues p d) γ = _
        rw [complete_present S.privateValues p
          ⟨d, DA.scope_subset d, hd⟩]
        exact hag _
      · rw [show T.profile (.inl d) = S.profile (.inl d) from
          complete_future S.privateValues p d (not_le.mp hd)]
    | inr d => exact hvcap d

