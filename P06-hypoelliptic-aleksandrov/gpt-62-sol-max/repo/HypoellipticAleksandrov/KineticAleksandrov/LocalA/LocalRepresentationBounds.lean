module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.LocalRepresentationTransport

/-! # Continuity, boundedness and measurability of supported local residuals -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Filter MeasureTheory Parabolic
open scoped Topology

section
variable {d : ℕ} (Z₀ : KineticPoint d) {R a T : ℝ} (hR : 0 < R) (ha : Z₀.time ≤ a)
  (hT : T ≤ Z₀.time + R ^ 2) (u : KineticPoint d → ℝ)
  (hu : ContinuousOn u (closure (forwardCylinder Z₀ R hR))) (χ : PDE.Vec d → ℝ)
  (hs : tsupport χ ⊆ PDE.euclideanBall 0 (R ^ 3)) (f : KineticPoint d → ℝ) (hf : Continuous f)
  (hz : ∀ Q, relativePosition Z₀ Q ∉ tsupport χ → f Q = 0)
include hR ha hT hu χ hs hf hz

/-- Compact outer-cylinder data bound every position-supported strip multiplier. -/
theorem localRepresentation_supported_mul_bounded :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ Q ∈ localClosedStrip a T Z₀.velocity R, |f Q * u Q| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closure_forwardCylinder Z₀ R hR).bddAbove_image
    (hf.continuousOn.mul hu).abs
  refine ⟨max M 0, le_max_right _ _, fun Q hQ => ?_⟩
  by_cases hx : relativePosition Z₀ Q ∈ tsupport χ
  · exact (hM ⟨Q, local_closed_strip_mem_outer Z₀ Q hR ha hT hQ (hs hx), rfl⟩).trans
      (le_max_left _ _)
  · rw [hz Q hx, zero_mul, abs_zero]
    exact le_max_right _ _

end

/-- A continuous strip residual has a measurable literal zero extension. -/
theorem localRepresentation_indicator_measurable {d : ℕ} (a T : ℝ)
    (v₀ : PDE.Vec d) (R : ℝ) (F : KineticPoint d → ℝ)
    (hF : ContinuousOn F (localStrip a T v₀ R)) :
    Measurable ((localStrip a T v₀ R).indicator F) := by
  classical
  exact hF.measurable_piecewise continuousOn_const (measurableSet_localStrip a T v₀ R)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
