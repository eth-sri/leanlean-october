/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalGradeOneLift
public import VaughtConjecture.Knight.CanonicalCoatomBountiful
public import VaughtConjecture.Knight.CanonicalSeedCoding

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalOneCoatom

open Transform Value ExtOrd CoatomBoundaryExtension AmalgamationPlan

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (sem : Semantics D) (hA : 1 ≤ A.card)
  (hp : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ 1)

abbrev scheme := CanonicalFieldLayer.scheme sem 1 (Cell D) id (by decide) hA

abbrev rows := CanonicalFieldLayer.rows sem 1 (Cell D) id (by decide) hA hp hg

abbrev old := CanonicalFieldLayer.old sem 1 (Cell D) id (by decide) hA

theorem coverage (d : Cell (scheme sem hA)) :
    (∃ c, old sem hA c = d) ∨ (scheme sem hA).scope d = A := by
  obtain ⟨c, rfl⟩ := (SourceLayerCarrier.enumeration D
    (CanonicalFieldLayer.Profile sem 1 (Cell D) id) 1 (by decide) hA).surjective d
  rcases c with c | c
  · exact Or.inl ⟨c, rfl⟩
  · exact Or.inr (congrArg Prod.fst (SourceLayerCarrier.cell_toCell _ _ _ _ _ _))

theorem complete
    (hc : ∀ J ∈ Plan.gradedPlan D.plan, J.1 ≠ A → ∃ d, D.cell d = J)
    (J : Finset ι × ℕ) (hJ : J ∈ Plan.gradedPlan D.plan) (hj : J.2 ≤ 1) :
    ∃ d, (scheme sem hA).cell d = J := by
  by_cases hs : J.1 = A
  · have h : J.2 = 1 := by have := (Plan.mem_gradedPlan.mp hJ).2.1; omega
    let c := CanonicalFieldLayer.controller sem 1 (Cell D) id (by decide) hA
      (CanonicalFieldLayer.Profile.bot sem 1 (Cell D) id)
    exact ⟨c.1, c.2.trans (Prod.ext hs.symm h.symm)⟩
  · obtain ⟨d, hd⟩ := hc J hJ hs
    exact ⟨old sem hA d, (SourceLayerCarrier.cell_toCell _ _ _ _ _ (.inl d)).trans hd⟩

abbrev equiv (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1) :=
  GradeCutLayerCarrier.properEquiv D (CanonicalFieldLayer.Profile sem 1 (Cell D) id)
    1 (by decide) hA J hJ

theorem respects_iff (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1) (p : D.below J → ExtOrd) :
    RespectsSemanticsBelow sem J p ↔
      RespectsSemanticsBelow (rows sem hA hp hg) J (p ∘ (equiv sem hA J hJ).symm) :=
  respects_iff_of_index_equiv (equiv sem hA J hJ)
    (fun d => SourceLayerCarrier.cell_toCell D _ 1 (by decide) hA (.inl d.1))
    (fun c d _ => (CanonicalFieldLayer.inherited_row sem 1 (Cell D) id (by decide) hA hp hg c.1 d).symm) p

theorem pullback {J : Finset ι × ℕ} (hJ : ¬ A ⊆ J.1)
    {q : (scheme sem hA).below J → ExtOrd} (hq : RespectsSemanticsBelow (rows sem hA hp hg) J q) :
    RespectsSemanticsBelow sem J (q ∘ equiv sem hA J hJ) :=
  (iff_comp_symm (equiv sem hA J hJ).symm (respects_iff sem hA hp hg J hJ) q).mp hq

theorem proper_lift {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : ¬ A ⊆ J.1)
    (hl : CappedLift sem h) : CappedLift (rows sem hA hp hg) h := by
  have hI : ¬ A ⊆ I.1 := fun hi => hJ (hi.trans h.1)
  exact CappedLift.of_equiv (equiv sem hA I hI) (equiv sem hA J hJ)
    (fun _ => rfl) le_rfl (respects_iff sem hA hp hg I hI) (respects_iff sem hA hp hg J hJ) hl

/-- Literal tops are decoded from proper representatives, not inserted into the catalogue. -/
theorem exists_whole {p : Cell D → ExtOrd} (hpr : RespectsSemantics sem p) :
    ∃ r : Cell (scheme sem hA) → ExtOrd, RespectsSemantics (rows sem hA hp hg) r ∧
      ∀ d, r (old sem hA d) = p d := by
  let all (d : Cell D) : D.below (A, 1) :=
    ⟨d, D.scope_subset d, hg d⟩
  obtain ⟨S, u, hu, _, hcode, hdecode⟩ :=
    (hpr.toBelow (A, 1)).exists_coded_representative (fun d => hg d.1)
      (le_refl (Nat.card (D.below (A, 1))))
  let v : Cell D → ExtOrd := fun d => u (all d)
  have hv : RespectsSemantics sem (v ∘ id) := hu.toRespects (fun d => (all d).2)
  have ht (d : Cell D) : v d ≠ ⊤ := by
    rcases mem_codedAlphabet_iff.mp (hcode (all d)) with hb | ⟨b, i, _, _, he⟩
    · exact hb.trans_ne bot_ne_top
    · exact he.trans_ne (ofOrd_ne_top _)
  let s := CanonicalFieldLayer.sectionOf sem 1 (Cell D) id (by decide) hA hp hg hv ht ∅ ⊤
  have hs := CanonicalFieldLayer.section_lawful sem 1 (Cell D) id (by decide) hA hp hg hv ht
    (G := ∅) (by simp) (extVisibilityReplace_top 1 1)
  let all' (d : Cell (scheme sem hA)) : (scheme sem hA).below (A, 1) :=
    ⟨d, (scheme sem hA).scope_subset d,
      CanonicalFieldLayer.max_grade sem 1 (Cell D) id (by decide) hA hg d⟩
  have hd := (hs.toBelow (A, 1)).decoded S (fun d => d.2.2)
  refine ⟨fun d => canonicalDecoder S 1 (s d), hd.toRespects (fun d => (all' d).2), ?_⟩
  intro d
  exact (congrArg (canonicalDecoder S 1)
    (CanonicalFieldLayer.section_old sem 1 (Cell D) id (by decide) hA hp hg hv ht
      (G := ∅) (by simp) (extVisibilityReplace_top 1 1) d)).trans (hdecode (all d))

variable (hold : CanonicalCoatomBountiful.OldLifts sem) {L R : Finset ι}

variable (hL : L ∈ D.plan) (hR : R ∈ D.plan) (hLA : L ≠ A) (hRA : R ≠ A)
  (hLc : 1 ≤ L.card) (hRc : 1 ≤ R.card) (hO : L ∩ R ∈ D.plan)
  (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)
  (hcomplete : ∀ C ∈ D.plan, C ≠ A → 1 ≤ C.card → ∃ d, D.cell d = (C, 1))

include hold hL hR hLA hRA hLc hRc hO hcover hcomplete in
theorem full_left {C : Finset ι} (hC : C ∈ D.plan) (hCA : C ≠ A) (hCc : 1 ≤ C.card)
    (hCL : C ⊆ L) : CappedLift (rows sem hA hp hg)
      (show GradedLe (C, 1) (A, 1) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by
  let h : GradedLe (C, 1) (A, 1) := ⟨D.isPlan.subset_of_mem hC, le_rfl⟩
  have hn : ¬ A ⊆ C := fun hh => hCA (Finset.Subset.antisymm h.1 hh)
  let W : CutCover sem (C, 1) 1 := CanonicalCoatomBountiful.oldCover sem hold hL hR hLA hRA hO (by decide : 0 < 1)
    hLc hRc (Plan.mem_gradedPlan.mpr ⟨hC, Nat.zero_lt_one, hCc⟩) ⟨hCL, le_rfl⟩
    (fun d => hcover _ (D.scope_mem_plan d) (hp d))
  intro p q γ hpr hqr hγ hag
  let e := equiv sem hA (C, 1) hn
  have hpr' := pullback sem hA hp hg hn hpr
  by_cases hb : γ = ⊥
  · obtain ⟨b, hbr, hread⟩ := W.section_of hg hpr'
    obtain ⟨r, hrr, he⟩ := exists_whole sem hA hp hg hbr
    refine ⟨fun d => r d.1, hrr.toBelow (A, 1), fun _ => by simp only [hb, min_bot_right], ?_⟩
    intro d
    obtain ⟨a, rfl⟩ := e.surjective d
    exact (he a.1).trans (hread a)
  · obtain ⟨c, hc⟩ := hcomplete C hC hCA hCc
    have hf : ∃ c : D.below (C, 1), D.cell c.1 = (C, 1) :=
      ⟨⟨c, by rw [hc]; exact GradedLe.refl _⟩, hc⟩
    obtain ⟨r, hrr, he, hcap⟩ := CanonicalGradeOneLift.exists_positive_lift
      sem (Cell D) id hA hp hg Function.injective_id hf hpr' hqr hγ hb
      (fun d => (hag (e d)).symm) W
    refine ⟨r, hrr, hcap, ?_⟩
    intro d
    obtain ⟨a, rfl⟩ := e.surjective d
    exact he a

include hold hL hR hLA hRA hLc hRc hO hcover hcomplete in
theorem bountiful : (rows sem hA hp hg).IsBountiful := by
  apply EffectiveGradeLifting.bountiful_of_bounded_same_grade
    (CanonicalFieldLayer.max_grade sem 1 (Cell D) id (by decide) hA hg) (by decide : 0 < 1)
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

end

end VaughtConjecture.Knight.CanonicalOneCoatom
