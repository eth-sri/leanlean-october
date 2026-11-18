/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RelativeLift
public import VaughtConjecture.Knight.CappedDonorFace
public import VaughtConjecture.Knight.CappedDonorReceiving

@[expose] public section

namespace VaughtConjecture.Knight.Growth
open Transform Value ExtOrd AmalgamationPlan
noncomputable section
variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}

structure State (DA : CellScheme A) (DQ : CellScheme Q) where
  privateValues : Cell DA → ExtOrd
  donorValues : Cell DQ → ExtOrd

abbrev Field (DA : CellScheme A) (DQ : CellScheme Q) := Cell DA ⊕ Cell DQ

namespace State
def profile (S : State DA DQ) : Field DA DQ → ExtOrd :=
  Sum.elim S.privateValues S.donorValues

/-- Recover both complete vectors, including fields above the current cutoff. -/
def ofProfile (a : Field DA DQ → ExtOrd) : State DA DQ :=
  ⟨fun d => a (.inl d), fun d => a (.inr d)⟩

@[simp] theorem ofProfile_profile (S : State DA DQ) : ofProfile S.profile = S := rfl

@[simp] theorem profile_ofProfile (a : Field DA DQ → ExtOrd) :
    (ofProfile a).profile = a := by
  funext f
  cases f <;> rfl

theorem profile_injective : Function.Injective (profile (DA := DA) (DQ := DQ)) := by
  intro S T h
  simpa only [ofProfile_profile] using congrArg ofProfile h

def map (σ : ExtOrd → ExtOrd) (S : State DA DQ) : State DA DQ :=
  ⟨σ ∘ S.privateValues, σ ∘ S.donorValues⟩

theorem profile_map (σ : ExtOrd → ExtOrd) (S : State DA DQ) (f : Field DA DQ) :
    (S.map σ).profile f = σ (S.profile f) := by cases f <;> rfl

def CapEq (γ : ExtOrd) (S T : State DA DQ) : Prop :=
  ∀ f, min (T.profile f) γ = min (S.profile f) γ

end State

variable (X : RelativeData DA semA DQ semQ)

/-- Complete root agreement is retained independently of relation activation.
The private and donor vectors include all future occurrences. -/
structure Admitted (j : ℕ) (S : State DA DQ) : Prop where
  private_lawful : RespectsSemanticsBelow semA (A, j) (fun d => S.privateValues d.1)
  donor_lawful : RespectsSemanticsBelow semQ (Q, j) (fun d => S.donorValues d.1)
  visible : ∀ f, SelfVis 1 (S.profile f)
  shared : ∀ d : DQ.below X.root, S.donorValues d.1 = S.privateValues (X.κ d).1
  correct : X.req.N ≤ j → InClass X.ZA S.privateValues →
    X.req.Correct (X.req.sec S.privateValues) S.donorValues

theorem Admitted.down {i j : ℕ} {S : State DA DQ} (hS : Admitted X j S) (hij : i ≤ j) :
    Admitted X i S where
  private_lawful := RespectsSemanticsBelow.mono
    (CI := (A, i)) (BJ := (A, j)) ⟨Finset.Subset.refl _, hij⟩ hS.private_lawful
  donor_lawful := RespectsSemanticsBelow.mono
    (CI := (Q, i)) (BJ := (Q, j)) ⟨Finset.Subset.refl _, hij⟩ hS.donor_lawful
  visible := hS.visible
  shared := hS.shared
  correct hN := hS.correct (hN.trans hij)

def zero : State DA DQ := ⟨fun _ => ⊥, fun _ => ⊥⟩

theorem zero_admitted (j : ℕ) : Admitted X j (zero (DA := DA) (DQ := DQ)) where
  private_lawful := respectsBelow_bot semA (A, j)
  donor_lawful := respectsBelow_bot semQ (Q, j)
  visible f := by cases f <;> exact selfVis_bot _
  shared _ := rfl
  correct _ hc := (X.C_notin ((hc X.req.capCell).mp rfl)).elim

def capAt {j : ℕ} (hj : X.req.N ≤ j) (d : DA.below (DA.cell X.req.C)) :
    DA.below (A, j) :=
  ⟨d.1, DA.isPlan.subset_of_mem (DA.scope_mem_plan d.1),
    d.2.2.trans (X.grade_C.le.trans hj)⟩

theorem zeroAbove_cap {j : ℕ} (hj : X.req.N ≤ j)
    (p : DA.below (A, j) → ExtOrd) (d : DA.below (DA.cell X.req.C)) :
    CellScheme.zeroAbove p d.1 = p (capAt X hj d) :=
  CellScheme.zeroAbove_low p (capAt X hj d)

theorem zeroAbove_capEq {j : ℕ} {p q : DA.below (A, j) → ExtOrd} {γ : ExtOrd}
    (h : ∀ d, min (p d) γ = min (q d) γ) (d : Cell DA) :
    min (CellScheme.zeroAbove p d) γ = min (CellScheme.zeroAbove q d) γ := by
  by_cases hd : DA.grade d ≤ j
  · exact (congrArg (min · γ) (CellScheme.zeroAbove_low p
      ⟨d, DA.isPlan.subset_of_mem (DA.scope_mem_plan d), hd⟩)).trans
      ((h _).trans (congrArg (min · γ) (CellScheme.zeroAbove_low q
        ⟨d, DA.isPlan.subset_of_mem (DA.scope_mem_plan d), hd⟩)).symm)
  · rw [CellScheme.zeroAbove_high p hd, CellScheme.zeroAbove_high q hd]

/-- Restore the future bookkeeping coordinates after the temporary zero tail. -/
def complete {j : ℕ} (u : Cell DA → ExtOrd) (p : DA.below (A, j) → ExtOrd)
    (d : Cell DA) : ExtOrd :=
  if hd : DA.grade d ≤ j then
    p ⟨d, DA.isPlan.subset_of_mem (DA.scope_mem_plan d), hd⟩ else u d

theorem complete_present {j : ℕ} (u : Cell DA → ExtOrd)
    (p : DA.below (A, j) → ExtOrd) (d : DA.below (A, j)) : complete u p d.1 = p d := by
  have hd : DA.grade d.1 ≤ j := d.2.2
  rw [complete, dite_eq_left hd]
  rfl

theorem complete_future {j : ℕ} (u : Cell DA → ExtOrd)
    (p : DA.below (A, j) → ExtOrd) (d : Cell DA) (hd : j < DA.grade d) :
    complete u p d = u d := by rw [complete, dite_eq_right (not_le.mpr hd)]

/-- All-cap active private repair on the actual full-scope grade cutoff.
Neither the replacement donor nor its correctness is an input. Future private
fields, and every complete-field original cap, are retained. -/
theorem private_repair {j : ℕ} (hj : X.req.N ≤ j) {S : State DA DQ}
    (hS : Admitted X j S) {p : DA.below (A, j) → ExtOrd}
    (hp : RespectsSemanticsBelow semA (A, j) p) {γ : ExtOrd} (hγ : SelfVis j γ)
    (hag : ∀ d, min (p d) γ = min (S.privateValues d.1) γ) :
    ∃ T : State DA DQ, Admitted X j T ∧
      (∀ d : DA.below (A, j), T.privateValues d.1 = p d) ∧ S.CapEq γ T ∧
      ∀ d, j < DA.grade d → T.privateValues d = S.privateValues d := by
  let u₀ := CellScheme.zeroAbove (fun d : DA.below (A, j) => S.privateValues d.1)
  have hsec : X.req.sec u₀ = X.req.sec S.privateValues :=
    funext (fun d => zeroAbove_cap X hj
      (fun d : DA.below (A, j) => S.privateValues d.1) d)
  have hcls : InClass X.ZA u₀ ↔ InClass X.ZA S.privateValues := by
    unfold InClass
    simp only [show ∀ d : DA.below (DA.cell X.req.C), u₀ d.1 = S.privateValues d.1
      from fun d => zeroAbove_cap X hj _ d]
  have hv : RespectsSemantics semQ S.donorValues := by
    exact hS.donor_lawful.toRespects (fun d =>
      ⟨DQ.isPlan.subset_of_mem (DQ.scope_mem_plan d), (X.grade_le d).trans hj⟩)
  have hall : X.Allowed u₀ S.donorValues :=
    ⟨hS.private_lawful.zeroAbove, hv,
      fun d => (hS.shared d).trans (zeroAbove_cap X hj
        (fun d : DA.below (A, j) => S.privateValues d.1) (X.κ d)).symm,
      fun hc => hsec.symm ▸ hS.correct hj (hcls.mp hc)⟩
  obtain ⟨v, hv, hvcap⟩ := X.relative_lift hall hp.zeroAbove (hγ.mono hj)
    (zeroAbove_capEq hag)
  let T : State DA DQ := ⟨complete S.privateValues p, v⟩
  have hcapread (d : DA.below (DA.cell X.req.C)) :
      T.privateValues d.1 = CellScheme.zeroAbove p d.1 :=
    (complete_present S.privateValues p (capAt X hj d)).trans (zeroAbove_cap X hj p d).symm
  refine ⟨T, ?_, complete_present S.privateValues p, ?_, complete_future S.privateValues p⟩
  · refine ⟨?_, hv.2.1.toBelow _, ?_, ?_, ?_⟩
    · simpa only [T, complete_present] using hp
    · intro f
      cases f with
      | inl d =>
        by_cases hd : DA.grade d ≤ j
        · have hpv : SelfVis (DA.grade d)
              (p ⟨d, DA.isPlan.subset_of_mem (DA.scope_mem_plan d), hd⟩) :=
            (hp.orderly ⟨d, DA.isPlan.subset_of_mem (DA.scope_mem_plan d), hd⟩).symm
          change SelfVis 1 (complete S.privateValues p d)
          rw [complete_present S.privateValues p
            ⟨d, DA.isPlan.subset_of_mem (DA.scope_mem_plan d), hd⟩]
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
          ⟨d, DA.isPlan.subset_of_mem (DA.scope_mem_plan d), hd⟩]
        exact hag _
      · rw [show T.profile (.inl d) = S.profile (.inl d) from
          complete_future S.privateValues p d (not_le.mp hd)]
    | inr d => exact hvcap d

end

open Transform Value ExtOrd AmalgamationPlan CappedDonor
noncomputable section

section Nominal
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

def cutoffEquiv (B : Finset ι) (j : ℕ) :
    D.below (B, min j B.card) ≃ D.below (B, j) where
  toFun d := ⟨d.1, d.2.1, (le_min_iff.mp d.2.2).1⟩
  invFun d := ⟨d.1, d.2.1, le_min d.2.2
    ((D.grade_le_card_scope d.1).trans (Finset.card_le_card d.2.1))⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem cutoff_respects {sem : Semantics D} (B : Finset ι) (j : ℕ)
    (p : D.below (B, min j B.card) → ExtOrd) :
    RespectsSemanticsBelow sem (B, min j B.card) p ↔
      RespectsSemanticsBelow sem (B, j) (p ∘ (cutoffEquiv B j).symm) :=
  respects_iff_of_equiv (cutoffEquiv B j) (fun _ => rfl) (fun _ _ => Iff.rfl)
    (fun _ _ _ => rfl) p

/-- Original-scheme lifting at a nominal cutoff, including an empty filtered
root. The output remains on the actual full original lower domain. -/
theorem extend_cutoff {sem : Semantics D} (hb : sem.IsBountiful)
    {B : Finset ι} (hB : B ∈ D.plan) {j : ℕ}
    {p : D.below (B, j) → ExtOrd} {q : D.below (A, j) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (B, j) p)
    (hq : RespectsSemanticsBelow sem (A, j) q)
    {γ : ExtOrd} (hγ : SelfVis j γ)
    (hag : ∀ d, min (q (CellScheme.below.mono
      (show GradedLe (B, j) (A, j) from ⟨D.isPlan.subset_of_mem hB, le_rfl⟩) d)) γ =
        min (p d) γ) :
    ∃ q', RespectsSemanticsBelow sem (A, j) q' ∧
      (∀ d, min (q' d) γ = min (q d) γ) ∧
      ∀ d, q' (CellScheme.below.mono
        (show GradedLe (B, j) (A, j) from ⟨D.isPlan.subset_of_mem hB, le_rfl⟩) d) = p d := by
  by_cases hz : 0 < min j B.card
  · have hsub := D.isPlan.subset_of_mem hB
    have hp' : RespectsSemanticsBelow sem (B, min j B.card)
        (p ∘ cutoffEquiv B j) := (cutoff_respects B j _).mpr hp
    have hq' : RespectsSemanticsBelow sem (A, min j A.card)
        (q ∘ cutoffEquiv A j) := (cutoff_respects A j _).mpr hq
    obtain ⟨r, hr, hcap, hread⟩ := hb.extend
      (Plan.mem_gradedPlan.mpr ⟨hB, hz, min_le_right _ _⟩)
      (Plan.mem_gradedPlan.mpr ⟨D.isPlan.domain_mem,
        hz.trans_le (min_le_min_left j (Finset.card_le_card hsub)), min_le_right _ _⟩)
      ⟨hsub, min_le_min_left j (Finset.card_le_card hsub)⟩ hp' hq'
      (hγ.mono (min_le_left _ _)) (fun d => hag (cutoffEquiv B j d))
    exact ⟨r ∘ (cutoffEquiv A j).symm, (cutoff_respects A j r).mp hr,
      fun d => hcap ((cutoffEquiv A j).symm d),
      fun d => hread ((cutoffEquiv B j).symm d)⟩
  · refine ⟨q, hq, fun _ => rfl, fun d => ?_⟩
    exact (hz ((D.grade_pos d.1).trans_le ((cutoffEquiv B j).symm d).2.2)).elim
end Nominal

variable {n J r : ℕ} {P : SemScheme (n + 1)} {C : SemScheme J}
  (F : SemScheme r) (fP : Fin r ↪ Fin (n + 1))
  (hvP : Finset.univ.image fP ∈ P.scheme.plan) (hP : P.restrictFace fP hvP = F)
  (fC : Fin r ↪ Fin J) (hvC : Finset.univ.image fC ∈ C.scheme.plan)
  (hC : C.restrictFace fC hvC = F)

abbrev rootMap (j : ℕ) := commonFace fP hvP hP fC hvC hC j

theorem rootMap_grade (j : ℕ) (a : P.scheme.below (Finset.univ.image fP, j)) :
    C.scheme.grade (rootMap F fP hvP hP fC hvC hC j a).1 = P.scheme.grade a.1 :=
  commonFace_grade fP hvP hP fC hvC hC j a

theorem rootMap_lawful (j : ℕ) (p : C.scheme.below (Finset.univ.image fC, j) → ExtOrd) :
    RespectsSemanticsBelow C.rows (Finset.univ.image fC, j) p ↔
      RespectsSemanticsBelow P.rows (Finset.univ.image fP, j)
        (fun a => p (rootMap F fP hvP hP fC hvC hC j a)) :=
  commonFace_respects fP hvP hP fC hvC hC j p

/-- The actual relative-data occurrence map, constructed from literal face
restrictions and containment of the private root in the cap's lower domain. -/
def literalKappa (c : Cell C.scheme)
    (hc : GradedLe (Finset.univ.image fC, r) (C.scheme.cell c)) :
    P.scheme.below (Finset.univ.image fP, r) → C.scheme.below (C.scheme.cell c) :=
  fun a => CellScheme.below.mono hc (rootMap F fP hvP hP fC hvC hC r a)

theorem literalKappa_lawful (c : Cell C.scheme)
    (hc : GradedLe (Finset.univ.image fC, r) (C.scheme.cell c))
    {s : C.scheme.below (C.scheme.cell c) → ExtOrd}
    (hs : RespectsSemanticsBelow C.rows (C.scheme.cell c) s) :
    RespectsSemanticsBelow P.rows (Finset.univ.image fP, r)
      (fun a => s (literalKappa F fP hvP hP fC hvC hC c hc a)) :=
  (rootMap_lawful F fP hvP hP fC hvC hC r _).mp (hs.mono hc)

/-- Only actual literal geometry is supplied. Grade preservation and all
filtered transports below are derived, not fields of this record. -/
structure RootAttachment (X : RelativeData C.scheme C.rows P.scheme P.rows) where
  root_eq : X.root = (Finset.univ.image fP, r)
  occurrence : ∀ a : P.scheme.below X.root,
    (X.κ a).1 = (rootMap F fP hvP hP fC hvC hC r
      ⟨a.1, root_eq ▸ a.2⟩).1

namespace RootAttachment
variable {F fP hvP hP fC hvC hC}
  {X : RelativeData C.scheme C.rows P.scheme P.rows}
  (R : RootAttachment F fP hvP hP fC hvC hC X)

include R in
theorem grade (a : P.scheme.below X.root) : C.scheme.grade (X.κ a).1 = P.scheme.grade a.1 := by
  rw [R.occurrence a]
  exact rootMap_grade _ _ _ _ _ _ _ _ _

def full {j : ℕ} (a : P.scheme.below (Finset.univ.image fP, j)) :
    P.scheme.below X.root :=
  ⟨a.1, R.root_eq.symm ▸ show GradedLe (P.scheme.cell a.1)
      (Finset.univ.image fP, r) from ⟨a.2.1, by
    change P.scheme.grade a.1 ≤ r
    have h := (P.scheme.grade_le_card_scope a.1).trans (Finset.card_le_card a.2.1)
    simpa only [Finset.card_image_of_injective _ fP.injective, Finset.card_univ,
      Fintype.card_fin] using h⟩⟩

theorem at_occurrence {j : ℕ} (a : P.scheme.below (Finset.univ.image fP, j)) :
    (rootMap F fP hvP hP fC hvC hC j a).1 = (X.κ (R.full a)).1 := by
  rw [R.occurrence]
  exact commonFace_val_congr _ _ _ _ _ _ _ _ _ rfl

def filtered {j : ℕ} (a : P.scheme.below X.root) (hj : P.scheme.grade a.1 ≤ j) :
    P.scheme.below (Finset.univ.image fP, j) :=
  ⟨a.1, (show GradedLe (P.scheme.cell a.1) (Finset.univ.image fP, r) from
    R.root_eq ▸ a.2).1, hj⟩

end RootAttachment
end
end VaughtConjecture.Knight.Growth
