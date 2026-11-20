/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveFullLift
public import VaughtConjecture.Knight.CanonicalCoatomBountiful

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveBountiful

open Transform Value ExtOrd CoatomBoundaryExtension AmalgamationPlan

open CanonicalRecursiveSuccessorRows CanonicalRecursiveCutPrefix CanonicalRecursiveActiveLift

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (sem : Semantics D) (n : ℕ) (hA : n + 3 ≤ A.card)

variable (hp : ∀ d : Cell D, D.scope d ≠ A)

variable (hb : CanonicalRecursiveRestoration.LowerBountiful sem n hA
  (predecessorState sem n hA hp))

variable (hold : CanonicalCoatomBountiful.OldLifts sem) {L R : Finset ι}

variable (hL : L ∈ D.plan) (hR : R ∈ D.plan) (hLA : L ≠ A) (hRA : R ≠ A)

variable (hLc : n + 3 ≤ L.card) (hRc : n + 3 ≤ R.card) (hO : L ∩ R ∈ D.plan)

variable (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)

variable (hcomplete : ∀ C ∈ D.plan, C ≠ A → n + 3 ≤ C.card →
  ∃ d : Cell D, D.cell d = (C, n + 3))

include hb hold hL hR hLA hRA hLc hRc hO hcover hcomplete in
theorem full_left {C : Finset ι} (hC : C ∈ D.plan) (hCA : C ≠ A)
    (hCc : n + 3 ≤ C.card) (hCL : C ⊆ L) :
    CappedLift (outputRows sem n hA hp)
      (show GradedLe (C, n + 3) (A, n + 3) from
        ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by
  let W := CanonicalCoatomBountiful.oldCover sem hold hL hR hLA hRA hO
    (by omega : 0 < n + 3) hLc hRc (I := (C, n + 3))
    (Plan.mem_gradedPlan.mpr ⟨hC, by omega, hCc⟩)
    ⟨hCL, le_rfl⟩ (fun d => hcover _ (D.scope_mem_plan d) (hp d))
  have hfull : ∃ c : (cut (D := D) n).below (C, n + 3),
      (cut (D := D) n).cell c.1 = (C, n + 3) := by
    obtain ⟨d, hd⟩ := hcomplete C hC hCA hCc
    have hgd : D.grade d ≤ n + 3 := (congrArg Prod.snd hd).le
    let c := GradeCutBoundary.fromCell D (n + 3) d hgd
    have hc : (cut (D := D) n).cell c = (C, n + 3) := by
      change D.cell (GradeCutBoundary.toCell D (n + 3) c) = _
      rw [GradeCutBoundary.to_from, hd]
    exact ⟨⟨c, by rw [hc]; exact GradedLe.refl _⟩, hc⟩
  exact CanonicalRecursiveFullLift.full_lift sem n hA hp hC hCA
    (GradeCutLifting.cutCover sem (n + 3) W) hb hCc hfull

include hb hold hL hR hLA hRA hLc hRc hO hcover hcomplete in
theorem full_lift {C : Finset ι} (hC : C ∈ D.plan) (hCA : C ≠ A)
    (hCc : n + 3 ≤ C.card) :
    CappedLift (outputRows sem n hA hp)
      (show GradedLe (C, n + 3) (A, n + 3) from
        ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by
  rcases hcover C hC hCA with hl | hr
  · exact full_left sem n hA hp hb hold hL hR hLA hRA hLc hRc hO hcover hcomplete
      hC hCA hCc hl
  · exact full_left sem n hA hp hb hold hR hL hRA hLA hRc hLc
      (Finset.inter_comm L R ▸ hO) (fun C hC hCA => (hcover C hC hCA).symm)
      hcomplete hC hCA hCc hr

include hb hold hL hR hLA hRA hLc hRc hO hcover hcomplete in
/-- Exhaustive literal-pair ledger on the enlarged actual grade cut.
The original permitted cap is unchanged, including bottom and literal top. -/
theorem bountiful :
    (GradeCutBoundary.rows (carrier sem n hA) (n + 3) (outputRows sem n hA hp)).IsBountiful := by
  apply EffectiveGradeLifting.bountiful_of_bounded_same_grade
    (GradeCutBoundary.grade_bound (carrier sem n hA) (n + 3)) (by omega)
  intro C B i hC hB hi hCB
  change (C, i) ∈ Plan.gradedPlan (carrier sem n hA).plan at hC
  change (B, i) ∈ Plan.gradedPlan (carrier sem n hA).plan at hB
  have hc : (C, i) ∈ Plan.gradedPlan D.plan := by
    simpa only [carrier_eq_recursive, CanonicalRecursiveBoundaryTransport.plan_eq] using hC
  have hb' : (B, i) ∈ Plan.gradedPlan D.plan := by
    simpa [carrier_eq_recursive, CanonicalRecursiveBoundaryTransport.plan_eq] using hB
  apply (GradeCutLifting.lift_iff (outputRows sem n hA hp) (n + 3) _ hi).mpr
  by_cases hil : i ≤ n + 2
  · apply CanonicalRecursiveLifting.lower_lift (CanonicalRecursiveSemantics.step sem hp n hA) _ hil
    apply (GradeCutLifting.lift_iff (predecessorState sem n hA hp).rows (n + 2) _ hil).mp
    apply lift_of_bountiful hb
    all_goals trivial
  have hik : i = n + 3 := by omega
  subst i
  by_cases hBA : B = A
  · subst B
    by_cases hCA : C = A
    · subst C; exact lift_refl
    · exact full_lift sem n hA hp hb hold hL hR hLA hRA hLc hRc hO hcover hcomplete
        (Plan.mem_gradedPlan.mp hc).1 hCA (Plan.mem_gradedPlan.mp hc).2.2
  · apply CanonicalRecursiveBoundaryTransport.proper_lift sem hp n hA _
      (fun h => hBA (Finset.Subset.antisymm
        (D.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hb').1) h))
    solve_by_elim

end

end VaughtConjecture.Knight.CanonicalRecursiveBountiful
