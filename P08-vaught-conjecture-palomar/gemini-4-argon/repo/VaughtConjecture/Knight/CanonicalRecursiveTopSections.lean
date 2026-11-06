/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveBoundaryTransport
public import VaughtConjecture.Knight.CoatomBoundaryExtension
public import VaughtConjecture.Knight.CanonicalCoatomBountiful
public import VaughtConjecture.Knight.GradeCutLifting

/-! # Literal-top boundary sections on the constructed recursive carrier -/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalRecursiveTopSections
open Transform Value ExtOrd CanonicalRecursiveContract CoatomBoundaryExtension AmalgamationPlan

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (hp : ∀ d : Cell D, D.scope d ≠ A)
  (n : ℕ) (hA : n + 3 ≤ A.card)

def boundaryTarget (d : D.below (A, n + 3)) : (carrier sem n hA).below (A, n + 3) :=
  ⟨boundary sem n hA d.1, by
    rw [CanonicalRecursiveInventory.boundary_cell]
    exact d.2⟩

theorem exists_section {p : D.below (A, n + 3) → ExtOrd}
    (hpr : RespectsSemanticsBelow sem (A, n + 3) p) :
    ∃ r : (carrier sem n hA).below (A, n + 3) → ExtOrd,
      RespectsSemanticsBelow (CanonicalRecursiveSemantics.rows sem hp n hA) (A, n + 3) r ∧
      ∀ d, r (boundaryTarget sem n hA d) = p d := by
  classical
  obtain ⟨S, u, hu, htop, hdecode⟩ := hpr.exists_coded_representative (fun d => d.2.2)
  let v : Cell D → ExtOrd := fun d => if hd : D.grade d ≤ n + 3 then
    u ⟨d, D.isPlan.subset_of_mem (D.scope_mem_plan d), hd⟩ else ⊥
  have hv (d : D.below (A, n + 3)) : v d.1 = u d := dite_eq_left d.2.2
  have hvr : RespectsSemanticsBelow sem (A, n + 3) (fun d => v d.1) := by simpa only [hv] using hu
  have hvt (d : Cell D) : v d ≠ ⊤ := by dsimp only [v]; split_ifs with hd <;> [exact htop _; exact bot_ne_top]
  let T := CanonicalRecursiveSemantics.state sem hp n hA
  let w := T.sectionOf le_rfl hvr hvt ∅ ⊤
  refine ⟨fun d => canonicalDecoder S (n + 3) (w d.1),
    (T.section_lawful le_rfl hvr hvt (by simp) (extVisibilityReplace_top _ _)).decoded S (fun d => d.2.2),
    fun d => (congrArg (canonicalDecoder S (n + 3))
      ((T.section_boundary le_rfl hvr hvt (G := ∅) (by simp)
        (extVisibilityReplace_top (n + 3) (n + 3)) d.1).trans (hv d))).trans (hdecode d)⟩

def faceEquiv (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1) (hj : J.2 ≤ n + 3) :
    (GradeCutBoundary.scheme D (n + 3)).below J ≃ (carrier sem n hA).below J :=
  (GradeCutBoundary.belowEquiv D (n + 3) J hj).trans
    (CanonicalRecursiveBoundaryTransport.properEquiv sem n hA J hJ)

theorem faceEquiv_val (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1) (hj : J.2 ≤ n + 3)
    (d : (GradeCutBoundary.scheme D (n + 3)).below J) :
    (faceEquiv sem n hA J hJ hj d).1 =
      boundary sem n hA (GradeCutBoundary.toCell D (n + 3) d.1) :=
  CanonicalRecursiveBoundaryTransport.properEquiv_val sem n hA J hJ _

theorem pullback_respects (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1) (hj : J.2 ≤ n + 3)
    {p : (carrier sem n hA).below J → ExtOrd}
    (hpr : RespectsSemanticsBelow (CanonicalRecursiveSemantics.rows sem hp n hA) J p) :
    RespectsSemanticsBelow (GradeCutBoundary.rows D (n + 3) sem) J
      (p ∘ faceEquiv sem n hA J hJ hj) :=
  GradeCutBoundary.pullback_respects D (n + 3) sem hj
    (CanonicalRecursiveBoundaryTransport.pullback_respects sem hp n hA J hJ hpr)

theorem exists_local_section {C : Finset ι} (hC : C ∈ D.plan) (hCA : C ≠ A)
    {U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell (GradeCutBoundary.scheme D (n + 3)),
      GradedLe ((GradeCutBoundary.scheme D (n + 3)).cell d) U ∨
      GradedLe ((GradeCutBoundary.scheme D (n + 3)).cell d) V)
    (hCU : GradedLe (C, n + 3) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell (GradeCutBoundary.scheme D (n + 3)),
      GradedLe ((GradeCutBoundary.scheme D (n + 3)).cell d) U →
      GradedLe ((GradeCutBoundary.scheme D (n + 3)).cell d) V →
      GradedLe ((GradeCutBoundary.scheme D (n + 3)).cell d) O)
    (hleft : CappedLift (GradeCutBoundary.rows D (n + 3) sem) hCU)
    (hright : CappedLift (GradeCutBoundary.rows D (n + 3) sem) hOV)
    {p : (carrier sem n hA).below (C, n + 3) → ExtOrd}
    (hpr : RespectsSemanticsBelow (CanonicalRecursiveSemantics.rows sem hp n hA) (C, n + 3) p) :
    ∃ r : (carrier sem n hA).below (A, n + 3) → ExtOrd,
      RespectsSemanticsBelow (CanonicalRecursiveSemantics.rows sem hp n hA) (A, n + 3) r ∧
      ∀ e, r (CellScheme.below.mono
        (show GradedLe (C, n + 3) (A, n + 3) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e) = p e := by
  have hCnot : ¬ A ⊆ C := fun h => hCA (Finset.Subset.antisymm (D.isPlan.subset_of_mem hC) h)
  let E := faceEquiv sem n hA (C, n + 3) hCnot le_rfl
  obtain ⟨b, hbread⟩ := CoatomBoundaryExtension.section_left
    hCU hOU hOV hinter hleft hright (p ∘ E)
    (pullback_respects sem hp n hA (C, n + 3) hCnot le_rfl hpr)
  let F := GradeCutBoundary.belowEquiv D (n + 3) (A, n + 3) le_rfl
  obtain ⟨r, hr, hread⟩ := exists_section sem hp n hA
    ((GradeCutBoundary.respects_iff D (n + 3) sem (A, n + 3) le_rfl _).mp
      ((b.whole_respects hcover).toBelow (A, n + 3)))
  refine ⟨r, hr, fun e => ?_⟩
  obtain ⟨d, rfl⟩ := E.surjective e
  let dA : (GradeCutBoundary.scheme D (n + 3)).below (A, n + 3) :=
    ⟨d.1, d.2.1.trans (D.isPlan.subset_of_mem hC), d.2.2⟩
  have hd : CellScheme.below.mono
      (show GradedLe (C, n + 3) (A, n + 3) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) (E d) =
      boundaryTarget sem n hA (F dA) :=
    Subtype.ext (faceEquiv_val sem n hA _ hCnot le_rfl d)
  rw [hd, hread]
  change b.whole hcover (F.symm (F dA)).1 = p (E d)
  rw [Equiv.symm_apply_apply]
  exact (b.whole_left hcover (CellScheme.below.mono hCU d)).trans
    ((b.value_left _).symm.trans (hbread d))

theorem bountiful_of_full
    (hold : CanonicalCoatomBountiful.OldLifts sem) {L R : Finset ι}
    (hL : L ∈ D.plan) (hR : R ∈ D.plan) (hLA : L ≠ A) (hRA : R ≠ A)
    (hLc : n + 3 ≤ L.card) (hRc : n + 3 ≤ R.card) (hO : L ∩ R ∈ D.plan)
    (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → n + 3 ≤ C.card →
      ∃ d : Cell D, D.cell d = (C, n + 3))
    (hlow : ∀ {C B : Finset ι} {i : ℕ} (h : GradedLe (C, i) (B, i)),
      (C, i) ∈ Plan.gradedPlan D.plan → (B, i) ∈ Plan.gradedPlan D.plan →
      i ≤ n + 2 → CappedLift (CanonicalRecursiveSemantics.rows sem hp n hA) h)
    (hfull_step : ∀ {C L R : Finset ι} (hC : C ∈ D.plan), C ≠ A →
      (∀ d : Cell (GradeCutBoundary.scheme D (n + 3)),
        GradedLe ((GradeCutBoundary.scheme D (n + 3)).cell d) (L, n + 3) ∨
        GradedLe ((GradeCutBoundary.scheme D (n + 3)).cell d) (R, n + 3)) →
      ∀ (hCL : GradedLe (C, n + 3) (L, n + 3)),
        CappedLift (GradeCutBoundary.rows D (n + 3) sem) hCL →
        CappedLift (GradeCutBoundary.rows D (n + 3) sem)
          (target_le_right (U := (L, n + 3)) (V := (R, n + 3))) →
        n + 3 ≤ C.card →
        (∃ c : (GradeCutBoundary.scheme D (n + 3)).below (C, n + 3),
          (GradeCutBoundary.scheme D (n + 3)).cell c.1 = (C, n + 3)) →
        CappedLift (CanonicalRecursiveSemantics.rows sem hp n hA)
          (show GradedLe (C, n + 3) (A, n + 3) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩)) :
    (GradeCutBoundary.rows (carrier sem n hA) (n + 3)
      (CanonicalRecursiveSemantics.rows sem hp n hA)).IsBountiful := by
  have hleft_step {C L R : Finset ι} (hL : L ∈ D.plan) (hR : R ∈ D.plan)
      (hLA : L ≠ A) (hRA : R ≠ A) (hLc : n + 3 ≤ L.card) (hRc : n + 3 ≤ R.card)
      (hO : L ∩ R ∈ D.plan) (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)
      (hC : C ∈ D.plan) (hCA : C ≠ A) (hCc : n + 3 ≤ C.card) (hCL : C ⊆ L) :
      CappedLift (CanonicalRecursiveSemantics.rows sem hp n hA)
        (show GradedLe (C, n + 3) (A, n + 3) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by
    have cover (d : Cell (GradeCutBoundary.scheme D (n + 3))) :
        GradedLe ((GradeCutBoundary.scheme D (n + 3)).cell d) (L, n + 3) ∨
        GradedLe ((GradeCutBoundary.scheme D (n + 3)).cell d) (R, n + 3) :=
      (hcover _ (D.scope_mem_plan _) (hp (GradeCutBoundary.toCell D (n + 3) d))).imp
        (fun h => ⟨h, GradeCutBoundary.grade_bound D _ d⟩)
        (fun h => ⟨h, GradeCutBoundary.grade_bound D _ d⟩)
    have left : CappedLift (GradeCutBoundary.rows D (n + 3) sem)
        (show GradedLe (C, n + 3) (L, n + 3) from ⟨hCL, le_rfl⟩) :=
      (GradeCutLifting.lift_iff sem (n + 3) _ le_rfl).mpr
        (hold (C, n + 3) (L, n + 3) (Plan.mem_gradedPlan.mpr ⟨hC, Nat.succ_pos _, hCc⟩)
          (Plan.mem_gradedPlan.mpr ⟨hL, Nat.succ_pos _, hLc⟩) hLA ⟨hCL, le_rfl⟩)
    have right : CappedLift (GradeCutBoundary.rows D (n + 3) sem)
        (target_le_right (U := (L, n + 3)) (V := (R, n + 3))) := by
      apply (GradeCutLifting.lift_iff sem (n + 3) _ le_rfl).mpr
      by_cases hne : (L ∩ R).Nonempty
      · exact hold _ _ (target_mem_gradedPlan hO (Nat.succ_pos _) (Nat.succ_pos _) hne)
          (Plan.mem_gradedPlan.mpr ⟨hR, Nat.succ_pos _, hRc⟩) hRA target_le_right
      · let := target_empty (D := D) (U := (L, n + 3)) (V := (R, n + 3))
          (Finset.not_nonempty_iff_eq_empty.mp hne)
        exact lift_empty target_le_right
    obtain ⟨d, hd⟩ := hcomplete C hC hCA hCc
    have hgd : D.grade d ≤ n + 3 := (congrArg Prod.snd hd).le
    let c := GradeCutBoundary.fromCell D (n + 3) d hgd
    have hc : (GradeCutBoundary.scheme D (n + 3)).cell c = (C, n + 3) :=
      (congrArg D.cell (GradeCutBoundary.to_from D (n + 3) d hgd)).trans hd
    exact hfull_step hC hCA cover ⟨hCL, le_rfl⟩ left right hCc
      ⟨⟨c, by rw [hc]; exact GradedLe.refl _⟩, hc⟩
  apply EffectiveGradeLifting.bountiful_of_bounded_same_grade
    (GradeCutBoundary.grade_bound (carrier sem n hA) (n + 3)) (Nat.succ_pos _)
  intro C B i hC hB hi hCB
  have hc : (C, i) ∈ Plan.gradedPlan D.plan := by
    rwa [← CanonicalRecursiveBoundaryTransport.plan_eq sem (n + 3) hA]
  have hb' : (B, i) ∈ Plan.gradedPlan D.plan := by
    rwa [← CanonicalRecursiveBoundaryTransport.plan_eq sem (n + 3) hA]
  apply (GradeCutLifting.lift_iff (CanonicalRecursiveSemantics.rows sem hp n hA) (n + 3) _ hi).mpr
  by_cases hil : i ≤ n + 2
  · exact hlow ⟨hCB, le_rfl⟩ hc hb' hil
  have hik : i = n + 3 := by omega
  subst i
  by_cases hBA : B = A
  · subst B
    by_cases hCA : C = A
    · subst C; exact lift_refl
    · rcases hcover C (Plan.mem_gradedPlan.mp hc).1 hCA with hl | hr
      · exact hleft_step hL hR hLA hRA hLc hRc hO hcover
          (Plan.mem_gradedPlan.mp hc).1 hCA (Plan.mem_gradedPlan.mp hc).2.2 hl
      · exact hleft_step hR hL hRA hLA hRc hLc (Finset.inter_comm L R ▸ hO)
          (fun C hC hCA => (hcover C hC hCA).symm)
          (Plan.mem_gradedPlan.mp hc).1 hCA (Plan.mem_gradedPlan.mp hc).2.2 hr
  · apply CanonicalRecursiveBoundaryTransport.proper_lift sem hp n hA _
      (fun h => hBA (Finset.Subset.antisymm
        (D.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hb').1) h))
    exact hold _ _ hc hb' hBA ⟨hCB, le_rfl⟩
