/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalSections
public import VaughtConjecture.Knight.CanonicalOwnerBoundary
public import VaughtConjecture.Knight.SingleFaceTailRestoration
public import VaughtConjecture.Knight.EffectiveGradeLifting
public import VaughtConjecture.Knight.HighLayerBountiful

/-! # Bountifulness of the fixed canonical two-grade coatom carrier

The inputs are old proper-face lifting, old grade-one/two completeness, and
the two-face plan geometry. No completion, locality, serving controller, or
lifting theorem for the output is supplied. Nominal higher grades are handled
at the actual grade ceiling, retaining their original permitted caps.
-/

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalGradeOneLift
open Transform Value ExtOrd SourcePrefixRows CanonicalFieldLayer CoatomBoundaryExtension
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (X : Type*) [Fintype X] (occ : Cell D → X)
variable (hA : 1 ≤ A.card) (hproper : ∀ d : Cell D, D.scope d ≠ A)
variable (hg : ∀ d : Cell D, D.grade d ≤ 1)

abbrev target := (scheme sem 1 X occ (by decide) hA).below (A, 1)
abbrev oldTarget (d : Cell D) : target sem X occ hA :=
  SourcePrefixAmbient.occurrence (data sem 1 X occ (by decide) hA hproper hg)
    (old sem 1 X occ (by decide) hA d)

private def botProfile : Profile sem 1 X occ :=
  encode sem 1 X occ hg (p := fun _ => ⊥) (RespectsSemantics.bot sem) (fun _ => bot_ne_top)

private theorem source_supp (b : Profile sem 1 X occ)
    (d : Cell (scheme sem 1 X occ (by decide) hA)) :
    OrbitPrefixSupport.Supported 1
      (PairedSlotComparison.sourceGrid 1 (Fintype.card X) : Set ExtOrd) b.val
      (source sem 1 X occ (by decide) hA hproper hg b d) := by
  let F := data sem 1 X occ (by decide) hA hproper hg
  by_cases he : (scheme sem 1 X occ (by decide) hA).cell d = (A, 1)
  · refine Or.inr (Or.inl ?_)
    change F.profile (controller sem 1 X occ (by decide) hA b) d ∈ F.grid
    rw [show d = (⟨d, he⟩ : SourcePrefixLayer.Controller _ 1).1 from rfl, F.profile_new]
    exact cut_mem F.bot_mem _ _
  · obtain ⟨e, rfl⟩ := SourceLayerCarrier.old_occurrence D (Profile sem 1 X occ)
      1 (by decide) hA d he
    rw [source_old]
    exact CanonicalOwnerBoundary.supported_self _ _ b.val (occ e)

private theorem exists_amb {q : target sem X occ hA → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem 1 X occ (by decide) hA hproper hg) (A, 1) q)
    (d : target sem X occ hA) (hd : (scheme sem 1 X occ (by decide) hA).grade d.1 = 1)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (_ : γ ≠ ⊥) (hactive : γ ≤ q d) :
    ∃ (a : Profile sem 1 X occ) (τ : ExtOrd → ExtOrd),
      Witness (gTop 1) τ ∧ (∀ z, τ z ≤ γ) ∧
      ∀ x : target sem X occ hA,
        τ (source sem 1 X occ (by decide) hA hproper hg a x.1) = min (q x) γ := by
  let F := data sem 1 X occ (by decide) hA hproper hg
  obtain ⟨c, τ, _, hτ, hb, _, hr⟩ := SourcePrefixAmbient.exists_active_source F
    (controller sem 1 X occ (by decide) hA (botProfile sem X occ hg)) hq d hd hγ hactive
  let a := member sem 1 X occ (by decide) hA hproper c
  have ha : controller sem 1 X occ (by decide) hA a = c :=
    (SeparatedSourceLayerCarrier.controllerEquiv D (Profile sem 1 X occ) 1 (by decide) hA
      (SeparatedSourceLayerCarrier.separated_of_proper D 1 hproper)).apply_symm_apply c
  refine ⟨a, τ, hτ, hb, fun x => ?_⟩
  change τ (F.profile (controller sem 1 X occ (by decide) hA a) x.1) = _
  rw [ha]
  exact hr x

theorem exists_positive_lift (hinj : Function.Injective occ) {C : Finset ι}
    (hfull : ∃ c : D.below (C, 1), D.cell c.1 = (C, 1))
    {p : D.below (C, 1) → ExtOrd} (hp : RespectsSemanticsBelow sem (C, 1) p)
    {q : target sem X occ hA → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem 1 X occ (by decide) hA hproper hg) (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e : D.below (C, 1), min (p e) γ =
      min (q (oldTarget sem X occ hA hproper hg e.1)) γ)
    {U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell D, GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (hCU : GradedLe (C, 1) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell D, GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hCU) (hright : CappedLift sem hOV)
    (hU : U.2 ≤ 1) (hV : V.2 ≤ 1) :
    ∃ r : target sem X occ hA → ExtOrd,
      RespectsSemanticsBelow (rows sem 1 X occ (by decide) hA hproper hg) (A, 1) r ∧
      (∀ e : D.below (C, 1), r (oldTarget sem X occ hA hproper hg e.1) = p e) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  obtain ⟨c, hci, hmax⟩ := AmbientGradeCharts.exists_maximizer hp hfull
  have hdom (e : D.below (C, 1)) : p e ≤ p c :=
    hmax e (Nat.le_antisymm (hg e.1) (D.grade_pos e.1))
  by_cases hactive : γ < p c
  · have hc : D.grade c.1 = 1 := congrArg Prod.snd hci
    have hcle : GradedLe (D.cell c.1) (C, 1) := by rw [hci]; exact GradedLe.refl _
    have hcU : GradedLe (D.cell c.1) U := hcle.trans hCU
    have hleftc : CappedLift sem hcU := by simpa only [hci] using hleft
    let F := data sem 1 X occ (by decide) hA hproper hg
    obtain ⟨r, hr, hread, hcap⟩ := CanonicalOwnerBoundary.exists_owner_capped_lift
      hinj hg (oldTarget sem X occ hA hproper hg)
      (fun d => by simp only [oldTarget, SourcePrefixAmbient.occurrence, old, CellScheme.grade,
        SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index])
      (source sem 1 X occ (by decide) hA hproper hg)
      (fun b => (F.profile_respects (controller sem 1 X occ (by decide) hA b)).toBelow (A, 1))
      (source_old sem 1 X occ (by decide) hA hproper hg)
      (source_supp sem X occ hA hproper hg)
      (source_prefix sem 1 X occ (by decide) hA hproper hg)
      (exists_amb sem X occ hA hproper hg)
      c.1 hc (hp.mono hcle) hq hγ hγb (fun e => hag ⟨e.1, e.2.trans hcle⟩)
      hactive hcover hcU hOU hOV hinter hleftc hright hU hV
    refine ⟨r, hr, fun e => ?_, hcap⟩
    exact (hread ⟨e.1, by rw [hci]; exact e.2⟩).trans (min_eq_left (hdom e))
  · exact ⟨fun d => min (q d) γ, hq.cap hγ,
      fun e => (hag e).symm.trans (min_eq_left ((hdom e).trans (not_lt.mp hactive))),
      fun _ => by rw [min_assoc, min_self]⟩

end
end VaughtConjecture.Knight.CanonicalGradeOneLift

namespace VaughtConjecture.Knight.CanonicalLowerLift
open Transform Value ExtOrd CanonicalMixedGradeLayers CoatomBoundaryExtension
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

theorem cut_lift {sem : Semantics D} {I U : Finset ι × ℕ} {j : ℕ}
    (h : GradedLe I U) (hU : U.2 ≤ j) (hlift : CappedLift sem h) :
    CappedLift (GradeCutBoundary.rows D j sem) h := by
  intro p q γ hp hq hγ hag
  let eI := GradeCutBoundary.belowEquiv D j I (h.2.trans hU)
  let eU := GradeCutBoundary.belowEquiv D j U hU
  have hp' := (GradeCutBoundary.respects_iff D j sem I (h.2.trans hU) p).mp hp
  have hq' := (GradeCutBoundary.respects_iff D j sem U hU q).mp hq
  have hm (d : (GradeCutBoundary.scheme D j).below I) :
      eU (CellScheme.below.mono h d) = CellScheme.below.mono h (eI d) := rfl
  have hms (d : D.below I) :
      eU.symm (CellScheme.below.mono h d) = CellScheme.below.mono h (eI.symm d) :=
    eU.injective (by rw [Equiv.apply_symm_apply, hm, Equiv.apply_symm_apply])
  obtain ⟨r, hr, hcap, hread⟩ := hlift (p ∘ eI.symm) (q ∘ eU.symm) γ hp' hq' hγ
    (fun d => by simpa only [Function.comp_apply, hms] using hag (eI.symm d))
  refine ⟨r ∘ eU, GradeCutBoundary.pullback_respects D j sem hU hr, ?_, ?_⟩
  · intro d; simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hcap (eU d)
  · intro d; simpa only [Function.comp_apply, hm, Equiv.symm_apply_apply] using hread (eI d)

end
end VaughtConjecture.Knight.CanonicalLowerLift

namespace VaughtConjecture.Knight.CanonicalCoatomBountiful
open Transform Value ExtOrd SourcePrefixRows CanonicalMixedGradeLayers
open CoatomBoundaryExtension AmalgamationPlan
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 2 ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ 2)

def OldLifts : Prop :=
  ∀ I J, I ∈ Plan.gradedPlan D.plan → J ∈ Plan.gradedPlan D.plan → J.1 ≠ A →
    (h : GradedLe I J) → CappedLift sem h

private abbrev outScheme := scheme sem 1 (by decide) (by omega) 2 (by decide) hA
private abbrev outRows := rows sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide)
private abbrev oldTarget :=
  CanonicalSections.oldTarget sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide)

private def properEquiv (BJ : Finset ι × ℕ) (hB : ¬ A ⊆ BJ.1) :
    D.below BJ ≃ (outScheme sem hA).below BJ :=
  (GradeCutLayerCarrier.properEquiv D (CanonicalGradeCutSections.Profiles sem 1)
    1 (by decide) (by omega) BJ hB).trans
    (GradeCutLayerCarrier.properEquiv (lowerScheme sem 1 (by decide) (by omega))
      (CanonicalFieldLayer.Profile sem 2 (Cell D) id) 2 (by decide) hA BJ hB)

private theorem properEquiv_cell (BJ : Finset ι × ℕ) (hB : ¬ A ⊆ BJ.1) (d : D.below BJ) :
    (outScheme sem hA).cell (properEquiv sem hA BJ hB d).1 = D.cell d.1 := by
  change (SourceLayerCarrier.scheme _ _ _ _ _).cell
    (SourceLayerCarrier.toCell _ _ _ _ _ (.inl
      (SourceLayerCarrier.toCell _ _ _ _ _ (.inl d.1)))) = _
  simp only [SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index]

private theorem proper_respects_iff (BJ : Finset ι × ℕ) (hB : ¬ A ⊆ BJ.1)
    (p : D.below BJ → ExtOrd) :
    RespectsSemanticsBelow sem BJ p ↔
      RespectsSemanticsBelow (outRows sem hA hproper hg) BJ
        (p ∘ (properEquiv sem hA BJ hB).symm) := by
  apply respects_iff_of_equiv (properEquiv sem hA BJ hB)
    (fun d => (congrArg Prod.snd (properEquiv_cell sem hA BJ hB d)).symm)
    (fun d e => ?_)
    (fun b d _ => (original_row sem 1 (by decide) (by omega) hproper 2 hg
      (by decide) hA (by decide) b.1 d).symm) p
  change (D.cell d.1).1 ⊆ (D.cell e.1).1 ↔ _
  simp only [CellScheme.scope, properEquiv_cell]

private theorem proper_lift {I J : Finset ι × ℕ} (h : GradedLe I J) (hB : ¬ A ⊆ J.1)
    (hlift : CappedLift sem h) : CappedLift (outRows sem hA hproper hg) h := by
  intro p q γ hp hq hγ hag
  have hC : ¬ A ⊆ I.1 := fun hc => hB (hc.trans h.1)
  let eI := properEquiv sem hA I hC
  let eJ := properEquiv sem hA J hB
  have pull (B : Finset ι × ℕ) (hBn : ¬ A ⊆ B.1)
      (u : (outScheme sem hA).below B → ExtOrd)
      (hu : RespectsSemanticsBelow (outRows sem hA hproper hg) B u) :
      RespectsSemanticsBelow sem B (u ∘ properEquiv sem hA B hBn) := by
    apply (proper_respects_iff sem hA hproper hg B hBn _).mpr
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using hu
  have hm (d : D.below I) : eJ (CellScheme.below.mono h d) = CellScheme.below.mono h (eI d) := rfl
  obtain ⟨r, hr, hcap, hread⟩ := hlift (p ∘ eI) (q ∘ eJ) γ
    (pull I hC p hp) (pull J hB q hq) hγ (fun d => hag (eI d))
  refine ⟨r ∘ eJ.symm, (proper_respects_iff sem hA hproper hg J hB r).mp hr,
    fun d => ?_, fun d => ?_⟩
  · simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hcap (eJ.symm d)
  · have hd : eJ.symm (CellScheme.below.mono h d) = CellScheme.below.mono h (eI.symm d) :=
      eJ.injective (by rw [Equiv.apply_symm_apply, hm, Equiv.apply_symm_apply])
    rw [Function.comp_apply, hd, hread]
    exact congrArg p (eI.apply_symm_apply d)

private def lowerEquiv :
    (CanonicalGradeCutSections.lower sem 1 (by decide) (by omega)).below (A, 1) ≃
      (outScheme sem hA).below (A, 1) :=
  (GradeCutLayerCarrier.belowEquiv D (CanonicalGradeCutSections.Profiles sem 1)
    1 (by decide) (by omega) (A, 1) le_rfl).trans
    (HighLayerBountiful.equiv (lowerScheme sem 1 (by decide) (by omega))
      (CanonicalFieldLayer.Profile sem 2 (Cell D) id) 2 (by decide) hA (A, 1)
      (fun he => by have := he.2; omega))

private theorem lower_respects_iff
    (p : (CanonicalGradeCutSections.lower sem 1 (by decide) (by omega)).below (A, 1) → ExtOrd) :
    RespectsSemanticsBelow
      (CanonicalGradeCutSections.lowerRows sem 1 (by decide) (by omega) hproper) (A, 1) p ↔
      RespectsSemanticsBelow (outRows sem hA hproper hg) (A, 1)
        (p ∘ (lowerEquiv sem hA).symm) := by
  refine (GradeCutLayerRows.lower_respects_iff D (CanonicalGradeCutSections.Profiles sem 1)
    1 (by decide) (by omega) hproper sem
    (CanonicalGradeCutSections.lowerRows sem 1 (by decide) (by omega) hproper)
    (CanonicalGradeCutSections.overlap sem 1 (by decide) (by omega) hproper)
    (A, 1) le_rfl p).trans ?_
  let e := HighLayerBountiful.equiv (lowerScheme sem 1 (by decide) (by omega))
    (CanonicalFieldLayer.Profile sem 2 (Cell D) id) 2 (by decide) hA (A, 1)
    (fun he => by have := he.2; omega)
  apply respects_iff_of_equiv e
    (fun d => (congrArg Prod.snd (HighLayerBountiful.equiv_cell
      (lowerScheme sem 1 (by decide) (by omega))
      (CanonicalFieldLayer.Profile sem 2 (Cell D) id) 2 (by decide) hA (A, 1) _ d)).symm)
    (fun d f => ?_)
    (fun b d _ => (inherited_row sem 1 (by decide) (by omega) hproper 2 hg
      (by decide) hA (by decide) b.1 d).symm)
  simp only [CellScheme.scope, e, HighLayerBountiful.equiv_cell]

private def botUpper : CanonicalFieldLayer.Profile sem 2 (Cell D) id :=
  CanonicalFieldLayer.encode sem 2 (Cell D) id hg (p := fun _ => ⊥)
    (RespectsSemantics.bot sem) (fun _ => bot_ne_top)

private theorem exists_amb_two
    {q : (outScheme sem hA).below (A, 2) → ExtOrd}
    (hq : RespectsSemanticsBelow (outRows sem hA hproper hg) (A, 2) q)
    (d : (outScheme sem hA).below (A, 2)) (hd : (outScheme sem hA).grade d.1 = 2)
    {γ : ExtOrd} (hγ : SelfVis 2 γ) (_ : γ ≠ ⊥) (hactive : γ ≤ q d) :
    ∃ (a : CanonicalFieldLayer.Profile sem 2 (Cell D) id) (τ : ExtOrd → ExtOrd),
      Witness (gTop 2) τ ∧ (∀ z, τ z ≤ γ) ∧
      ∀ x : (outScheme sem hA).below (A, 2),
        τ (source sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide) a x.1) =
          min (q x) γ := by
  let F := data sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide)
  obtain ⟨c, τ, _, hτ, hbound, _, hread⟩ := SourcePrefixAmbient.exists_active_source F
    (controller sem 1 (by decide) (by omega) 2 (by decide) hA (botUpper sem hg))
    hq d hd hγ hactive
  let a := member sem 1 (by decide) (by omega) hproper 2 (by decide) hA (by decide) c
  have ha : controller sem 1 (by decide) (by omega) 2 (by decide) hA a = c :=
    (SeparatedSourceLayerCarrier.controllerEquiv (lowerScheme sem 1 (by decide) (by omega))
      (CanonicalFieldLayer.Profile sem 2 (Cell D) id) 2 (by decide) hA
      (lower_separated sem 1 (by decide) (by omega) hproper 2 (by decide))).apply_symm_apply c
  refine ⟨a, τ, hτ, hbound, fun x => ?_⟩
  change τ (F.profile (controller sem 1 (by decide) (by omega) 2 (by decide) hA a) x.1) = _
  rw [ha]
  exact hread x

variable (hold : OldLifts sem)

include hold in
private theorem overlap_lift {L R : Finset ι} (hR : R ∈ D.plan) (hRA : R ≠ A)
    (hO : L ∩ R ∈ D.plan) {n : ℕ} (hn : 0 < n) (hnR : n ≤ R.card) :
    CappedLift sem (target_le_right (U := (L, n)) (V := (R, n))) := by
  by_cases hne : (L ∩ R).Nonempty
  · exact hold _ _ (target_mem_gradedPlan hO hn hn hne)
      (Plan.mem_gradedPlan.mpr ⟨hR, hn, hnR⟩) hRA target_le_right
  · let := target_empty (D := D) (U := (L, n)) (V := (R, n))
      (Finset.not_nonempty_iff_eq_empty.mp hne)
    exact lift_empty target_le_right

include hold in
private theorem full_lift_one {L R C : Finset ι}
    (hL : L ∈ D.plan) (hR : R ∈ D.plan) (hLA : L ≠ A) (hRA : R ≠ A)
    (hLc : 2 ≤ L.card) (hRc : 2 ≤ R.card) (hO : L ∩ R ∈ D.plan)
    (hcover : ∀ d : Cell D, D.scope d ⊆ L ∨ D.scope d ⊆ R)
    (hC : C ∈ D.plan) (hCA : C ≠ A) (hCL : C ⊆ L)
    (hfull₁ : C.Nonempty → ∃ c : D.below (C, 1), D.cell c.1 = (C, 1)) :
    CappedLift (outRows sem hA hproper hg)
      (show GradedLe (C, 1) (A, 1) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by
  let h : GradedLe (C, 1) (A, 1) := ⟨D.isPlan.subset_of_mem hC, le_rfl⟩
  have hCnot : ¬ A ⊆ C := fun ha => hCA (Finset.Subset.antisymm h.1 ha)
  let e := properEquiv sem hA (C, 1) hCnot
  intro p q γ hp hq hγ hag
  by_cases hne : C.Nonempty
  swap
  · refine ⟨q, hq, fun _ => rfl, fun d => ?_⟩
    obtain ⟨a, rfl⟩ := e.surjective d
    exact (hne (Finset.card_pos.mp ((D.grade_pos a.1).trans_le
      ((D.grade_le_card_scope a.1).trans (Finset.card_le_card a.2.1))))).elim
  have hC1 : (C, 1) ∈ Plan.gradedPlan D.plan :=
    Plan.mem_gradedPlan.mpr ⟨hC, (by decide : 0 < 1), Finset.card_pos.mpr hne⟩
  have cover₂ (d : Cell D) : GradedLe (D.cell d) (L, 2) ∨ GradedLe (D.cell d) (R, 2) :=
    (hcover d).imp (fun hd => ⟨hd, hg d⟩) (fun hd => ⟨hd, hg d⟩)
  have left₂ : CappedLift sem (show GradedLe (C, 1) (L, 2) from ⟨hCL, (by decide : 1 ≤ 2)⟩) :=
    hold (C, 1) (L, 2) hC1 (Plan.mem_gradedPlan.mpr ⟨hL, (by decide : 0 < 2), hLc⟩)
      hLA ⟨hCL, (by decide : 1 ≤ 2)⟩
  have left₁ : CappedLift sem (show GradedLe (C, 1) (L, 1) from ⟨hCL, le_rfl⟩) :=
    hold (C, 1) (L, 1) hC1
      (Plan.mem_gradedPlan.mpr ⟨hL, (by decide : 0 < 1), (by decide : 1 ≤ 2).trans hLc⟩)
      hLA ⟨hCL, le_rfl⟩
  have right₂ := overlap_lift sem hold hR hRA hO (by decide : 0 < 2) hRc
  have right₁ := overlap_lift sem hold hR hRA hO (by decide : 0 < 1) (by omega)
  have hp' : RespectsSemanticsBelow sem (C, 1) (p ∘ e) := by
    apply (proper_respects_iff sem hA hproper hg (C, 1) hCnot _).mpr
    simpa only [e, Function.comp_def, Equiv.apply_symm_apply] using hp
  by_cases hγb : γ = ⊥
  · obtain ⟨r, hr, hread⟩ := CanonicalSections.exists_section sem 1 (by decide) (by omega)
      hproper 2 hg (by decide) hA (by decide) cover₂
      (show GradedLe (C, 1) (L, 2) from ⟨hCL, (by decide : 1 ≤ 2)⟩) target_le_left
      target_le_right (fun d hl hr => (below_target_iff d).mpr ⟨hl, hr⟩) left₂ right₂ hp'
    let h12 : GradedLe (A, 1) (A, 2) := ⟨Finset.Subset.refl _, (by decide : 1 ≤ 2)⟩
    refine ⟨fun d => r (CellScheme.below.mono h12 d), hr.mono h12,
      fun _ => by simp only [hγb, min_bot_right], fun d => ?_⟩
    obtain ⟨a, rfl⟩ := e.surjective d
    exact hread a
  · let eC := GradeCutBoundary.belowEquiv D 1 (C, 1) le_rfl
    let eA := lowerEquiv sem hA
    have hp₁ := GradeCutBoundary.pullback_respects D 1 sem le_rfl hp'
    have hq₁ : RespectsSemanticsBelow
        (CanonicalGradeCutSections.lowerRows sem 1 (by decide) (by omega) hproper) (A, 1)
        (q ∘ eA) := by
      apply (lower_respects_iff sem hA hproper hg _).mpr
      simpa only [eA, Function.comp_def, Equiv.apply_symm_apply] using hq
    obtain ⟨c, hc⟩ := hfull₁ hne
    have hf : ∃ c : (GradeCutBoundary.scheme D 1).below (C, 1),
        (GradeCutBoundary.scheme D 1).cell c.1 = (C, 1) :=
      ⟨eC.symm c, (congrArg (fun z : D.below (C, 1) => D.cell z.1)
        (eC.apply_symm_apply c)).trans hc⟩
    have hmap (d : (GradeCutBoundary.scheme D 1).below (C, 1)) :
        eA (CanonicalGradeOneLift.oldTarget (GradeCutBoundary.rows D 1 sem) (Cell D)
          (GradeCutBoundary.toCell D 1) (by omega) (GradeCutBoundary.proper D 1 hproper)
          (GradeCutBoundary.grade_bound D 1) d.1) =
        CellScheme.below.mono h (e (eC d)) := by
      apply Subtype.ext
      change oldCell sem 1 (by decide) (by omega) 2 (by decide) hA
        (GradeCutLayerCarrier.embed D (CanonicalGradeCutSections.Profiles sem 1)
          1 (by decide) (by omega)
          (SourceLayerCarrier.toCell (GradeCutBoundary.scheme D 1)
            (CanonicalGradeCutSections.Profiles sem 1) 1 (by decide) (by omega) (.inl d.1))) = _
      rw [GradeCutLayerCarrier.embed_toCell]
      rfl
    have cover₁ (d : Cell (GradeCutBoundary.scheme D 1)) :
        GradedLe ((GradeCutBoundary.scheme D 1).cell d) (L, 1) ∨
        GradedLe ((GradeCutBoundary.scheme D 1).cell d) (R, 1) :=
      (hcover (GradeCutBoundary.toCell D 1 d)).imp
        (fun hs => ⟨hs, GradeCutBoundary.grade_bound D 1 d⟩)
        (fun hs => ⟨hs, GradeCutBoundary.grade_bound D 1 d⟩)
    obtain ⟨r, hr, hread, hcap⟩ := CanonicalGradeOneLift.exists_positive_lift
      (GradeCutBoundary.rows D 1 sem) (Cell D) (GradeCutBoundary.toCell D 1) (by omega)
      (GradeCutBoundary.proper D 1 hproper) (GradeCutBoundary.grade_bound D 1)
      (GradeCutBoundary.toCell D 1).injective hf hp₁ hq₁ hγ hγb
      (fun d => by
        change min (p (e (eC d))) γ = min (q (eA _)) γ
        rw [hmap]; exact (hag (e (eC d))).symm)
      cover₁ (show GradedLe (C, 1) (L, 1) from ⟨hCL, le_rfl⟩) target_le_left target_le_right
      (fun d hl hr => (below_target_iff (GradeCutBoundary.toCell D 1 d)).mpr ⟨hl, hr⟩)
      (CanonicalLowerLift.cut_lift (show GradedLe (C, 1) (L, 1) from ⟨hCL, le_rfl⟩) le_rfl left₁)
      (CanonicalLowerLift.cut_lift (target_le_right (U := (L, 1)) (V := (R, 1))) le_rfl right₁)
      le_rfl le_rfl
    refine ⟨r ∘ eA.symm, (lower_respects_iff sem hA hproper hg r).mp hr,
      fun d => ?_, fun d => ?_⟩
    · simpa only [Function.comp_apply, eA.apply_symm_apply] using hcap (eA.symm d)
    · obtain ⟨a, rfl⟩ := e.surjective d
      have hm := hmap (eC.symm a)
      rw [eC.apply_symm_apply] at hm
      rw [← hm, Function.comp_apply, eA.symm_apply_apply, hread]
      exact congrArg (p ∘ e) (eC.apply_symm_apply a)

include hold in
private theorem full_lift_left {L R C : Finset ι}
    (hL : L ∈ D.plan) (hR : R ∈ D.plan) (hLA : L ≠ A) (hRA : R ≠ A)
    (hLc : 2 ≤ L.card) (hRc : 2 ≤ R.card) (hO : L ∩ R ∈ D.plan)
    (hcover : ∀ d : Cell D, D.scope d ⊆ L ∨ D.scope d ⊆ R)
    (hC : C ∈ D.plan) (hCA : C ≠ A) (hCL : C ⊆ L)
    (hfull₁ : C.Nonempty → ∃ c : D.below (C, 1), D.cell c.1 = (C, 1))
    (hfull₂ : 2 ≤ C.card → ∃ c : D.below (C, 2), D.cell c.1 = (C, 2))
    {n : ℕ} (hn : 0 < n) (hn2 : n ≤ 2) (hnC : n ≤ C.card)
    (h : GradedLe (C, n) (A, n)) :
    CappedLift (outRows sem hA hproper hg) h := by
  have hlow := full_lift_one sem hA hproper hg hold hL hR hLA hRA hLc hRc hO
    hcover hC hCA hCL hfull₁
  have hncase : n = 1 ∨ n = 2 := by omega
  rcases hncase with rfl | rfl
  · exact hlow
  · have hCnot : ¬ A ⊆ C := fun ha => hCA (Finset.Subset.antisymm h.1 ha)
    let e := properEquiv sem hA (C, 2) hCnot
    have cover₂ (d : Cell D) : GradedLe (D.cell d) (L, 2) ∨ GradedLe (D.cell d) (R, 2) :=
      (hcover d).imp (fun hd => ⟨hd, hg d⟩) (fun hd => ⟨hd, hg d⟩)
    have left₂ : CappedLift sem (show GradedLe (C, 2) (L, 2) from ⟨hCL, le_rfl⟩) :=
      hold (C, 2) (L, 2) (Plan.mem_gradedPlan.mpr ⟨hC, (by decide : 0 < 2), hnC⟩)
        (Plan.mem_gradedPlan.mpr ⟨hL, (by decide : 0 < 2), hLc⟩) hLA ⟨hCL, le_rfl⟩
    have right₂ := overlap_lift sem hold hR hRA hO (by decide : 0 < 2) hRc
    intro p q γ hp hq hγ hag
    have hp' : RespectsSemanticsBelow sem (C, 2) (p ∘ e) := by
      apply (proper_respects_iff sem hA hproper hg (C, 2) hCnot _).mpr
      simpa only [e, Function.comp_def, Equiv.apply_symm_apply] using hp
    by_cases hγb : γ = ⊥
    · obtain ⟨r, hr, hread⟩ := CanonicalSections.exists_section sem 1 (by decide) (by omega)
        hproper 2 hg (by decide) hA (by decide) cover₂
        (show GradedLe (C, 2) (L, 2) from ⟨hCL, le_rfl⟩) target_le_left
        target_le_right (fun d hl hr => (below_target_iff d).mpr ⟨hl, hr⟩) left₂ right₂ hp'
      refine ⟨r, hr, fun _ => by simp only [hγb, min_bot_right], fun d => ?_⟩
      obtain ⟨a, rfl⟩ := e.surjective d
      exact hread a
    by_cases hactive : ∃ d : (outScheme sem hA).below (C, 2),
        (outScheme sem hA).grade d.1 = 2 ∧ γ < p d
    · obtain ⟨c, hci, hmax⟩ := AmbientGradeCharts.exists_maximizer hp' (hfull₂ hnC)
      let p₀ := p ∘ e
      let M := p₀ c
      have hpc : γ < M := by
        obtain ⟨d, hd, hpd⟩ := hactive
        obtain ⟨a, rfl⟩ := e.surjective d
        have ha : D.grade a.1 = 2 := by
          change ((outScheme sem hA).cell (e a).1).2 = 2 at hd
          rwa [properEquiv_cell] at hd
        exact hpd.trans_le (hmax a ha)
      have hc : D.grade c.1 = 2 := congrArg Prod.snd hci
      have hM : SelfVis 2 M := by simpa only [hc] using (hp'.orderly c).symm
      have hcle : GradedLe (D.cell c.1) (C, 2) := c.2
      have hcU : GradedLe (D.cell c.1) (L, 2) := hcle.trans ⟨hCL, le_rfl⟩
      have hl : CappedLift sem hcU := by simpa only [hci] using left₂
      let F := data sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide)
      have hold_grade (d : Cell D) :
          (outScheme sem hA).grade (oldTarget sem hA hproper hg d).1 = D.grade d := by
        change (SourceLayerCarrier.scheme _ _ _ _ _).grade
          (SourceLayerCarrier.toCell _ _ _ _ _ (.inl
            (SourceLayerCarrier.toCell _ _ _ _ _ (.inl d)))) = _
        simp only [CellScheme.grade, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index]
      obtain ⟨u, hu, hread, hcap⟩ := CanonicalOwnerBoundary.exists_owner_capped_lift
        Function.injective_id hg (oldTarget sem hA hproper hg) hold_grade
        (source sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide))
        (fun b => (F.profile_respects
          (controller sem 1 (by decide) (by omega) 2 (by decide) hA b)).toBelow (A, 2))
        (source_boundary sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide))
        (source_supported sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide))
        (source_agreement sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide))
        (exists_amb_two sem hA hproper hg)
        c.1 hc (hp'.mono hcle) hq hγ hγb
        (fun d => (hag (e ⟨d.1, d.2.trans hcle⟩)).symm) hpc
        cover₂ hcU target_le_left target_le_right
        (fun d hl hr => (below_target_iff d).mpr ⟨hl, hr⟩) hl right₂ le_rfl le_rfl
      have hreadPhys (d : (outScheme sem hA).below (C, 2)) :
          u (CellScheme.below.mono h d) = min (p d) M := by
        obtain ⟨a, rfl⟩ := e.surjective d
        exact hread ⟨a.1, by rw [hci]; exact a.2⟩
      have hmaxPhys (d : (outScheme sem hA).below (C, 2))
          (hd : (outScheme sem hA).grade d.1 = 2) : p d ≤ M := by
        obtain ⟨a, rfl⟩ := e.surjective d
        apply hmax a
        change ((outScheme sem hA).cell (e a).1).2 = 2 at hd
        rwa [properEquiv_cell] at hd
      obtain ⟨r, hr, hrlit, hrM, _⟩ := SingleFaceTailRestoration.exists_restore
        (outRows sem hA hproper hg) h.1 hlow hp hu hM hreadPhys hmaxPhys
      exact ⟨r, hr, fun d =>
        (GradeTailRestoration.cap_below (hrM d) hpc.le).trans (hcap d), hrlit⟩
    · exact SingleFaceTailRestoration.exists_inactive (outRows sem hA hproper hg)
        h.1 hlow hp hq hγ hag (fun d hd => not_lt.mp (fun ha => hactive ⟨d, hd, ha⟩))

include hold in
theorem bountiful {L R : Finset ι}
    (hL : L ∈ D.plan) (hR : R ∈ D.plan) (hLA : L ≠ A) (hRA : R ≠ A)
    (hLc : 2 ≤ L.card) (hRc : 2 ≤ R.card) (hO : L ∩ R ∈ D.plan)
    (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → ∀ i, 0 < i → i ≤ C.card → i ≤ 2 →
      ∃ d : Cell D, D.cell d = (C, i)) :
    (rows sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide)).IsBountiful := by
  apply EffectiveGradeLifting.bountiful_of_bounded_same_grade
    (fun d => (data sem 1 (by decide) (by omega) hproper 2 hg
      (by decide) hA (by decide)).max_grade d) (by decide : 0 < 2)
  intro C B i hCi hBi hi hCB
  change (C, i) ∈ Plan.gradedPlan D.plan at hCi
  change (B, i) ∈ Plan.gradedPlan D.plan at hBi
  by_cases hBA : B = A
  · subst B
    by_cases hCA : C = A
    · subst C; exact lift_refl
    have hc := Plan.mem_gradedPlan.mp hCi
    have hfull₁ (hne : C.Nonempty) : ∃ c : D.below (C, 1), D.cell c.1 = (C, 1) := by
      obtain ⟨c, he⟩ := hcomplete C hc.1 hCA 1 (by decide) (Finset.card_pos.mpr hne) (by decide)
      exact ⟨⟨c, by rw [he]; exact GradedLe.refl _⟩, he⟩
    have hfull₂ (hcard : 2 ≤ C.card) : ∃ c : D.below (C, 2), D.cell c.1 = (C, 2) := by
      obtain ⟨c, he⟩ := hcomplete C hc.1 hCA 2 (by decide) hcard le_rfl
      exact ⟨⟨c, by rw [he]; exact GradedLe.refl _⟩, he⟩
    have cells (d : Cell D) : D.scope d ⊆ L ∨ D.scope d ⊆ R :=
      hcover (D.scope d) (D.scope_mem_plan d) (hproper d)
    rcases hcover C hc.1 hCA with hl | hr
    · exact full_lift_left sem hA hproper hg hold hL hR hLA hRA hLc hRc hO cells
        hc.1 hCA hl hfull₁ hfull₂ hc.2.1 hi hc.2.2 ⟨hCB, le_rfl⟩
    · exact full_lift_left sem hA hproper hg hold hR hL hRA hLA hRc hLc
        (Finset.inter_comm L R ▸ hO) (fun d => (cells d).symm)
        hc.1 hCA hr hfull₁ hfull₂ hc.2.1 hi hc.2.2 ⟨hCB, le_rfl⟩
  · have hBnot : ¬ A ⊆ B := fun hb => hBA (Finset.Subset.antisymm
      (D.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hBi).1) hb)
    exact proper_lift sem hA hproper hg (I := (C, i)) (J := (B, i)) ⟨hCB, le_rfl⟩ hBnot
      (hold _ _ hCi hBi hBA ⟨hCB, le_rfl⟩)

end
end VaughtConjecture.Knight.CanonicalCoatomBountiful
