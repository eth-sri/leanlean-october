/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalGradeOneLift
public import VaughtConjecture.Knight.CanonicalCoatomBountiful
public import VaughtConjecture.Knight.CanonicalSeedCoding

/-! # The small grade-one coatom seed, at every original cap

The catalogue and rows are the existing canonical field layer. Old legal-face
lifts supply the boundary; no lift or completion of the output is assumed.
-/
@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalOneCoatom
open Transform Value ExtOrd CoatomBoundaryExtension AmalgamationPlan

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (hA : 1 ≤ A.card)
  (hp : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ 1)
abbrev scheme := CanonicalFieldLayer.scheme sem 1 (Cell D) id (by decide) hA
abbrev rows := CanonicalFieldLayer.rows sem 1 (Cell D) id (by decide) hA hp hg
abbrev old := CanonicalFieldLayer.old sem 1 (Cell D) id (by decide) hA
abbrev equiv (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1) :=
  GradeCutLayerCarrier.properEquiv D (CanonicalFieldLayer.Profile sem 1 (Cell D) id)
    1 (by decide) hA J hJ

theorem respects_iff (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1) (p : D.below J → ExtOrd) :
    RespectsSemanticsBelow sem J p ↔
      RespectsSemanticsBelow (rows sem hA hp hg) J (p ∘ (equiv sem hA J hJ).symm) := by
  apply respects_iff_of_equiv (equiv sem hA J hJ)
    (fun d => (congrArg Prod.snd (SourceLayerCarrier.cell_toCell D _ 1 (by decide) hA
      (.inl d.1))).symm) (fun d e => ?_) (fun c d _ => ?_) p
  · change (D.cell d.1).1 ⊆ (D.cell e.1).1 ↔
      ((scheme sem hA).cell (old sem hA d.1)).1 ⊆ ((scheme sem hA).cell (old sem hA e.1)).1
    simp only [old, CanonicalFieldLayer.old, SourceLayerCarrier.cell_toCell,
      SourceLayerCarrier.index]
  · exact (CanonicalFieldLayer.inherited_row sem 1 (Cell D) id (by decide) hA hp hg c.1 d).symm

theorem pullback {J : Finset ι × ℕ} (hJ : ¬ A ⊆ J.1)
    {q : (scheme sem hA).below J → ExtOrd} (hq : RespectsSemanticsBelow (rows sem hA hp hg) J q) :
    RespectsSemanticsBelow sem J (q ∘ equiv sem hA J hJ) := by
  apply (respects_iff sem hA hp hg J hJ _).mpr
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using hq

theorem proper_lift {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : ¬ A ⊆ J.1)
    (hl : CappedLift sem h) : CappedLift (rows sem hA hp hg) h :=
  have hI : ¬ A ⊆ I.1 := fun hi => hJ (hi.trans h.1)
  hl.of_respects_iff (equiv sem hA I hI) (equiv sem hA J hJ) (fun _ => rfl)
    (respects_iff sem hA hp hg I hI) (respects_iff sem hA hp hg J hJ)

/-- Literal tops are decoded from proper representatives, not inserted into the catalogue. -/
theorem exists_whole {p : Cell D → ExtOrd} (hpr : RespectsSemantics sem p) :
    ∃ r : Cell (scheme sem hA) → ExtOrd, RespectsSemantics (rows sem hA hp hg) r ∧
      ∀ d, r (old sem hA d) = p d := by
  obtain ⟨S, v, hv, ht, hdecode⟩ := hpr.exists_coded_representative hg
  let s := CanonicalFieldLayer.sectionOf sem 1 (Cell D) id (by decide) hA hp hg hv ht ∅ ⊤
  have hs := CanonicalFieldLayer.section_lawful sem 1 (Cell D) id (by decide) hA hp hg hv ht
    (G := ∅) (by simp) (extVisibilityReplace_top 1 1)
  have hd := (hs.toBelow (A, 1)).decoded S (fun d => d.2.2)
  refine ⟨fun d => canonicalDecoder S 1 (s d), hd.toRespects (fun d =>
    ⟨(scheme sem hA).isPlan.subset_of_mem ((scheme sem hA).scope_mem_plan d),
      (CanonicalFieldLayer.data sem 1 (Cell D) id (by decide) hA hp hg).max_grade d⟩), fun d =>
    (congrArg (canonicalDecoder S 1)
      (CanonicalFieldLayer.section_old sem 1 (Cell D) id (by decide) hA hp hg hv ht
        (G := ∅) (by simp) (extVisibilityReplace_top 1 1) d)).trans (hdecode d)⟩

variable (hold : CanonicalCoatomBountiful.OldLifts sem) {L R : Finset ι}
  (hL : L ∈ D.plan) (hR : R ∈ D.plan) (hLA : L ≠ A) (hRA : R ≠ A)
  (hLc : 1 ≤ L.card) (hRc : 1 ≤ R.card) (hO : L ∩ R ∈ D.plan)
  (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)
  (hcomplete : ∀ C ∈ D.plan, C ≠ A → 1 ≤ C.card → ∃ d, D.cell d = (C, 1))

include hold hL hR hLA hRA hLc hRc hO hcover hcomplete in
theorem full_left {C : Finset ι} (hC : C ∈ D.plan) (hCA : C ≠ A) (hCc : 1 ≤ C.card)
    (hCL : C ⊆ L) : CappedLift (rows sem hA hp hg)
      (show GradedLe (C, 1) (A, 1) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by
  let h : GradedLe (C, 1) (A, 1) := ⟨D.isPlan.subset_of_mem hC, le_rfl⟩
  have hn : ¬ A ⊆ C := fun hh => hCA (Finset.Subset.antisymm h.1 hh)
  have cover (d : Cell D) : GradedLe (D.cell d) (L, 1) ∨ GradedLe (D.cell d) (R, 1) :=
    (hcover _ (D.scope_mem_plan d) (hp d)).imp (fun hh => ⟨hh, hg d⟩) (fun hh => ⟨hh, hg d⟩)
  have hl : CappedLift sem (show GradedLe (C, 1) (L, 1) from ⟨hCL, le_rfl⟩) :=
    hold (C, 1) (L, 1) (Plan.mem_gradedPlan.mpr ⟨hC, (by decide : 0 < 1), hCc⟩)
      (Plan.mem_gradedPlan.mpr ⟨hL, (by decide : 0 < 1), hLc⟩) hLA ⟨hCL, le_rfl⟩
  have hr : CappedLift sem (target_le_right (U := (L, 1)) (V := (R, 1))) := by
    by_cases hne : (L ∩ R).Nonempty
    · exact hold _ _ (target_mem_gradedPlan hO (by decide : 0 < 1) (by decide : 0 < 1) hne)
        (Plan.mem_gradedPlan.mpr ⟨hR, (by decide : 0 < 1), hRc⟩) hRA target_le_right
    · let := target_empty (D := D) (U := (L, 1)) (V := (R, 1))
        (Finset.not_nonempty_iff_eq_empty.mp hne)
      exact lift_empty target_le_right
  intro p q γ hpr hqr hγ hag
  let e := equiv sem hA (C, 1) hn
  have hpr' := pullback sem hA hp hg hn hpr
  have inter (d : Cell D) (hl : GradedLe (D.cell d) (L, 1))
      (hr : GradedLe (D.cell d) (R, 1)) := (below_target_iff d).mpr ⟨hl, hr⟩
  by_cases hb : γ = ⊥
  · obtain ⟨b, hread⟩ := section_left (show GradedLe (C, 1) (L, 1) from ⟨hCL, le_rfl⟩)
      target_le_left target_le_right inter hl hr (p ∘ e) hpr'
    obtain ⟨r, hrr, he⟩ := exists_whole sem hA hp hg (b.whole_respects cover)
    refine ⟨fun d => r d.1, hrr.toBelow (A, 1), fun _ => by simp only [hb, min_bot_right], ?_⟩
    intro d
    obtain ⟨a, rfl⟩ := e.surjective d
    exact (he a.1).trans (hread a)
  · obtain ⟨c, hc⟩ := hcomplete C hC hCA hCc
    have hf : ∃ c : D.below (C, 1), D.cell c.1 = (C, 1) :=
      ⟨⟨c, by rw [hc]; exact GradedLe.refl _⟩, hc⟩
    obtain ⟨r, hrr, he, hcap⟩ := CanonicalGradeOneLift.exists_positive_lift
      sem (Cell D) id hA hp hg Function.injective_id hf hpr' hqr hγ hb
      (fun d => (hag (e d)).symm) cover ⟨hCL, le_rfl⟩ target_le_left target_le_right
      inter hl hr le_rfl le_rfl
    refine ⟨r, hrr, hcap, ?_⟩
    intro d
    obtain ⟨a, rfl⟩ := e.surjective d
    exact he a

include hold hL hR hLA hRA hLc hRc hO hcover hcomplete in
theorem bountiful : (rows sem hA hp hg).IsBountiful := by
  apply EffectiveGradeLifting.bountiful_of_bounded_same_grade
    (CanonicalFieldLayer.data sem 1 (Cell D) id (by decide) hA hp hg).max_grade (by decide : 0 < 1)
  intro C B j hC hB hj hCB
  have hj1 : j = 1 := by have := (Plan.mem_gradedPlan.mp hC).2.1; omega
  subst j
  by_cases hBA : B = A
  · subst B
    by_cases hCA : C = A
    · subst C; exact lift_refl
    have hc := Plan.mem_gradedPlan.mp hC
    rcases hcover C hc.1 hCA with hl | hr
    · exact full_left sem hA hp hg hold hL hR hLA hRA hLc hRc hO hcover hcomplete hc.1 hCA hc.2.2 hl
    · exact full_left sem hA hp hg hold hR hL hRA hLA hRc hLc
        (Finset.inter_comm L R ▸ hO) (fun C hC hCA => (hcover C hC hCA).symm)
        hcomplete hc.1 hCA hc.2.2 hr
  · exact proper_lift sem hA hp hg (I := (C, 1)) (J := (B, 1)) ⟨hCB, le_rfl⟩
      (fun hh => hBA (Finset.Subset.antisymm
        (D.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hB).1) hh))
      (hold _ _ hC hB hBA ⟨hCB, le_rfl⟩)
