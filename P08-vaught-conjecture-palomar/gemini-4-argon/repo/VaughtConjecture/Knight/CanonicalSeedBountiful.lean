/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalSeedFullLift
public import VaughtConjecture.Knight.CanonicalCoatomBountiful

/-! # Bountifulness of the actual recursive grade-three seed

The predecessor retains higher proper owners. Only its current grade cut is
supplied by the proved lower-pair theorem at initialization; this layer supplies
bountifulness at the grade-three cut.
Every proper row and occurrence remains literal, and the constructed state
already supplies the selected-section contract. Old coatom geometry and
old-face lifting remain explicit, separate from ordered installation.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalSeedBountiful
open Transform Value ExtOrd CoatomBoundaryExtension AmalgamationPlan CanonicalRecursiveSeedRows CanonicalSeedCutPrefix CanonicalSeedActiveLift

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (hA : 3 ≤ A.card)
  (hp : ∀ d : Cell D, D.scope d ≠ A)
  (hb : CanonicalSeedRestoration.LowerBountiful sem hA hp)
  (hold : CanonicalCoatomBountiful.OldLifts sem) {L R : Finset ι}
  (hL : L ∈ D.plan) (hR : R ∈ D.plan) (hLA : L ≠ A) (hRA : R ≠ A)
  (hLc : 3 ≤ L.card) (hRc : 3 ≤ R.card) (hO : L ∩ R ∈ D.plan)
  (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)
  (hcomplete : ∀ C ∈ D.plan, C ≠ A → 3 ≤ C.card →
  ∃ d : Cell D, D.cell d = (C, 3))

include hb hold hL hR hLA hRA hLc hRc hO hcover hcomplete in
theorem bountiful :
    (GradeCutBoundary.rows (carrier sem hA) 3 (outputRows sem hA hp)).IsBountiful :=
  CanonicalRecursiveTopSections.bountiful_of_full sem hp 0 hA hold hL hR hLA hRA
    hLc hRc hO hcover hcomplete
    (fun h hc hb' hil => CanonicalSeedLifting.lower_lift sem hA hp h hil
      ((GradeCutLifting.lift_iff (predecessorRows sem hA hp) 2 h hil).mp
        (lift_of_bountiful hb hc hb' h)))
    fun hC hCA cover hCL left right hCc hfull =>
      CanonicalSeedFullLift.full_lift sem hA hp hC hCA cover hCL
        target_le_left target_le_right
        (fun d hl hr => (below_target_iff d).mpr ⟨hl, hr⟩) left right hb hCc hfull le_rfl le_rfl
