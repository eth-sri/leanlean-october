/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveFullLift
public import VaughtConjecture.Knight.CanonicalCoatomBountiful

/-! # Bountifulness preservation at the recursive current grade

The predecessor retains higher proper owners. Only its current grade cut is
assumed bountiful; the successor supplies bountifulness at the enlarged cut.
Every proper row and occurrence remains literal, and the constructed state
already supplies the selected-section contract. Old coatom geometry and
old-face lifting remain explicit, separate from ordered installation.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalRecursiveBountiful
open Transform Value ExtOrd CoatomBoundaryExtension AmalgamationPlan CanonicalRecursiveSuccessorRows CanonicalRecursiveCutPrefix CanonicalRecursiveActiveLift

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
  (hp : ∀ d : Cell D, D.scope d ≠ A)
  (hb : CanonicalRecursiveRestoration.LowerBountiful sem n hA
  (predecessorState sem n hA hp))
  (hold : CanonicalCoatomBountiful.OldLifts sem) {L R : Finset ι}
  (hL : L ∈ D.plan) (hR : R ∈ D.plan) (hLA : L ≠ A) (hRA : R ≠ A)
  (hLc : n + 4 ≤ L.card) (hRc : n + 4 ≤ R.card) (hO : L ∩ R ∈ D.plan)
  (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)
  (hcomplete : ∀ C ∈ D.plan, C ≠ A → n + 4 ≤ C.card →
  ∃ d : Cell D, D.cell d = (C, n + 4))

include hb hold hL hR hLA hRA hLc hRc hO hcover hcomplete in
theorem bountiful :
    (GradeCutBoundary.rows (carrier sem n hA) (n + 4) (outputRows sem n hA hp)).IsBountiful :=
  CanonicalRecursiveTopSections.bountiful_of_full sem hp (n + 1) hA hold hL hR hLA hRA
    hLc hRc hO hcover hcomplete
    (fun h hc hb' hil => CanonicalRecursiveLifting.lower_lift sem n hA hp
      (predecessorState sem n hA hp) h hil
      ((GradeCutLifting.lift_iff (predecessorState sem n hA hp).rows (n + 3) h hil).mp
        (lift_of_bountiful hb
          (by change _ ∈ Plan.gradedPlan (predecessor sem n hA).plan
              rwa [CanonicalRecursiveBoundaryTransport.plan_eq])
          (by change _ ∈ Plan.gradedPlan (predecessor sem n hA).plan
              rwa [CanonicalRecursiveBoundaryTransport.plan_eq]) h)))
    fun hC hCA cover hCL left right hCc hfull =>
      CanonicalRecursiveFullLift.full_lift sem n hA hp hC hCA cover hCL
        target_le_left target_le_right
        (fun d hl hr => (below_target_iff d).mpr ⟨hl, hr⟩) left right hb hCc hfull le_rfl le_rfl
