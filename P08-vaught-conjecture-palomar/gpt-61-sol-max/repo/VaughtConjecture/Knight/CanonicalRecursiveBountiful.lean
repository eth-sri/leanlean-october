
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalRecursiveFullLift
import VaughtConjecture.Knight.CanonicalCoatomBountiful

/-! # Bountifulness preservation at the recursive current grade

The predecessor retains higher proper owners. Only its current grade cut is
assumed bountiful; the successor supplies bountifulness at the enlarged cut.
Every proper row and occurrence remains literal, and the constructed state
already supplies the selected-section contract. Old coatom geometry and
old-face lifting remain explicit, separate from ordered installation.
-/

namespace VaughtConjecture.Knight.CanonicalRecursiveBountiful
open    CoatomBoundaryExtension AmalgamationPlan
open CanonicalRecursiveSuccessorRows CanonicalRecursiveCutPrefix CanonicalRecursiveActiveLift

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
variable (hp : AvoidsValue D.scope A)
variable (hb : CanonicalRecursiveRestoration.LowerBountiful sem n hA
  (predecessorState sem n hA hp))
variable (hold : CanonicalCoatomBountiful.OldLifts sem) {L R : Finset ι}
variable (hL : L ∈ D.plan) (hR : R ∈ D.plan) (hLA : L ≠ A) (hRA : R ≠ A)
variable (hLc : n + 4 ≤ L.card) (hRc : n + 4 ≤ R.card) (hO : L ∩ R ∈ D.plan)
variable (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)
variable (hcomplete : ∀ C ∈ D.plan, C ≠ A → n + 4 ≤ C.card →
  ∃ d , D.cell d = (C, n + 4))

local notation "outputRows₀" => outputRows sem n hA hp

include hb hold hL hR hLA hRA hLc hRc hO hcover hcomplete in
theorem full_left {C} (hC : C ∈ D.plan) (hCA : C ≠ A)
    (hCc : n + 4 ≤ C.card) (hCL : C ⊆ L) :
    CappedLift (outputRows₀)
      (show GradedLe (C, n + 4) (A, n + 4) from
        ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by 
  let core1 := cut (D := D) n
  have cover (d : Cell (core1)) :
      GradedLe ((core1).cell d) (L, n + 4) ∨
      GradedLe ((core1).cell d) (R, n + 4) :=
    (hcover _ (D.scope_mem_plan _) (hp (occurrence (D := D) n d))).imp
      (fun h => ⟨h, GradeCutBoundary.grade_bound d⟩)
      (fun h => ⟨h, GradeCutBoundary.grade_bound d⟩)
  have left  :=
    (GradeCutLifting.lift_iff sem (n + 4) _ le_rfl).mpr
      (hold (C, n + 4) (L, n + 4) (Plan.mem_gradedPlan.mpr ⟨hC, by omega, hCc⟩)
        (Plan.mem_gradedPlan.mpr ⟨hL, by omega, hLc⟩) hLA ⟨hCL, le_rfl⟩)
  have right : CappedLift (cutRows sem n)
      (target_le_right (U := (L, n + 4)) (V := (R, n + 4))) := by
    apply (GradeCutLifting.lift_iff sem (n + 4) _ le_rfl).mpr
    by_cases hne : (L ∩ R).Nonempty
    · exact hold _ _ (target_mem_gradedPlan hO
        (by omega : 0 < n + 4) (by omega : 0 < n + 4) hne)
        (Plan.mem_gradedPlan.mpr ⟨hR, by omega, hRc⟩) hRA target_le_right
    · let := target_empty (D := D) (U := (L, n + 4)) (V := (R, n + 4))
        (Finset.not_nonempty_iff_eq_empty.mp hne)
      exact lift_empty target_le_right
  have hfull : ∃ c : (core1).below (C, n + 4),
      (core1).cell c.1 = (C, n + 4) := by
    obtain ⟨d, hd⟩ := hcomplete C hC hCA hCc
    have hgd : D.grade d ≤ n + 4 := (congrArg Prod.snd hd).le
    let c := GradeCutBoundary.fromCell D (n + 4) d hgd
    have hc : (core1).cell c = (C, n + 4) := by
      change D.cell (GradeCutBoundary.toCell D (n + 4) c) = _
      rw [GradeCutBoundary.to_from, hd]
    exact ⟨⟨c, by rw [hc]; exact GradedLe.refl _⟩, hc⟩
  exact CanonicalRecursiveFullLift.full_lift sem n hA hp hC hCA cover
    ⟨hCL, le_rfl⟩ target_le_left target_le_right
    (fun d hl hr => (below_target_iff d).mpr ⟨hl, hr⟩) left right hb hCc hfull le_rfl le_rfl

include hb hold hL hR hLA hRA hLc hRc hO hcover hcomplete in
theorem full_lift {C} (hC : C ∈ D.plan) (hCA : C ≠ A)
    (hCc : n + 4 ≤ C.card) :
    CappedLift (outputRows₀)
      (show GradedLe (C, n + 4) (A, n + 4) from
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
    (GradeCutBoundary.rows (carrier sem n hA) (n + 4) (outputRows₀)).IsBountiful := by
  apply EffectiveGradeLifting.bountiful_of_bounded_same_grade
    (GradeCutBoundary.grade_bound) (by omega)
  intro C B i hC hB hi hCB
  change (C, i) ∈ Plan.gradedPlan (carrier sem n hA).plan at hC
  change (B, i) ∈ Plan.gradedPlan (carrier sem n hA).plan at hB
  have hc  := by
    simpa only [carrier_eq_recursive, CanonicalRecursiveBoundaryTransport.plan_eq] using hC
  have hb'  := by
    simpa only [carrier_eq_recursive, CanonicalRecursiveBoundaryTransport.plan_eq] using hB
  apply (GradeCutLifting.lift_iff outputRows₀ (n + 4) _ hi).mpr
  by_cases hil : i ≤ n + 3
  · apply CanonicalRecursiveLifting.lower_lift sem n hA hp
      (predecessorState sem n hA hp) _ hil
    apply (GradeCutLifting.lift_iff (predecessorState sem n hA hp).rows (n + 3) _ hil).mp
    apply lift_of_bountiful hb
    · aesop
    · aesop
  have hik : i = n + 4 := by omega
  subst i
  by_cases hBA : B = A
  · subst B
    by_cases hCA : C = A
    · subst C; exact lift_refl
    · exact full_lift sem n hA hp hb hold hL hR hLA hRA hLc hRc hO hcover hcomplete
        (Plan.mem_gradedPlan.mp hc).1 hCA (Plan.mem_gradedPlan.mp hc).2.2
  · apply CanonicalRecursiveBoundaryTransport.proper_lift sem hp (n + 1) hA _
      (fun h => hBA (Finset.Subset.antisymm
        (D.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hb').1) h))
    exact hold _ _ hc hb' hBA ⟨hCB, le_rfl⟩


