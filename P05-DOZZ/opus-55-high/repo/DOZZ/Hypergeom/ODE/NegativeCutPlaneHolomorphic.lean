/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.NegativeCutPlaneLocalGluing

/-! The path-independent scalar endpoint is holomorphic on the negative cut plane. -/

@[expose] public section

open Filter Topology

namespace DOZZ.Proofs

/-- Extend the first component of the selected negative-cut endpoint state to a total function on ℂ.
Its values off the cut plane are immaterial. -/
noncomputable def gaussNegativeCutPlaneScalarState (a b c z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ gaussNegativeCutPlane then
    (gaussNegativeCutPlaneContinuationState a b c ⟨z, hz⟩).1
  else 0
section
variable (a b c : ℂ)

private theorem gaussNegativeCutPlaneScalarState_eq_picard_near
    (z : gaussNegativeCutPlane) :
    ∃ R r : ℝ, 0 < R ∧ 0 < r ∧ r ≤ R / 2 ∧
      ∃ D : HolomorphicDiskSolution (gaussSystemOperator a b c) R,
        D.center = (z : ℂ) ∧ Metric.ball (z : ℂ) r ⊆ gaussNegativeCutPlane ∧
        ∀ w ∈ Metric.ball (z : ℂ) r,
          gaussNegativeCutPlaneScalarState a b c w = (D.solution w).1 := by
  obtain ⟨R, δ, hR, hδ, hδR, D, hcenter, hlocal⟩ :=
    gaussNegativeCutPlaneContinuationState_locally_eq_picard a b c z
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp
    (gaussNegativeCutPlane_isOpen.mem_nhds z.property)
  let r := min δ ε
  have hrδ : r ≤ δ := min_le_left ..
  have hrε : r ≤ ε := min_le_right ..
  have hball : Metric.ball (z : ℂ) r ⊆ gaussNegativeCutPlane := by
    intro w hw
    exact hεball (Metric.ball_subset_ball hrε hw)
  refine ⟨R, r, hR, (lt_min hδ hε), le_trans hrδ hδR, D, hcenter, hball, ?_⟩
  intro w hw
  have hwcut := hball hw
  dsimp [gaussNegativeCutPlaneScalarState]
  rw [dite_eq_left hwcut]
  exact congrArg Prod.fst (hlocal ⟨w, hwcut⟩ (lt_of_lt_of_le (Metric.mem_ball.mp hw) hrδ))

/-- The first component of the path-independent negative-cut endpoint is holomorphic in the endpoint.
-/
theorem gaussNegativeCutPlaneScalarState_differentiableOn
    :
    DifferentiableOn ℂ (gaussNegativeCutPlaneScalarState a b c) gaussNegativeCutPlane := by
  intro z hz
  let z' : gaussNegativeCutPlane := ⟨z, hz⟩
  obtain ⟨R, r, hR, hr, hrR, D, hcenter, hball, hEq⟩ :=
    gaussNegativeCutPlaneScalarState_eq_picard_near a b c z'
  have hDmem : z ∈ Metric.ball D.center R := by
    aesop
  have hnear : gaussNegativeCutPlaneScalarState a b c =ᶠ[𝓝 z]
      (fun w => (D.solution w).1) := by
    filter_upwards [Metric.ball_mem_nhds z hr] with w hw
    tauto
  exact ((((D.derivative z hDmem).differentiableAt).fst).congr_of_eventuallyEq hnear).differentiableWithinAt

end

end DOZZ.Proofs
