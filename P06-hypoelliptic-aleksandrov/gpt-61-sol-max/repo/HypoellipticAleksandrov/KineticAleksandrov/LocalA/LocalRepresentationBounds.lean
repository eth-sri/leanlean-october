module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.LocalRepresentationTransport

/-! # Continuity, boundedness and measurability of supported local residuals -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Filter
open scoped Topology

variable {d : ℕ}

section
variable (Z₀ : KineticPoint d) {R a T : ℝ} (hR : 0 < R) (ha : Z₀.time ≤ a) (hT : T ≤ Z₀.time + R ^ 2) (u : HypoellipticAleksandrov.KineticScalarField d) (hu : ContinuousOn u (closure (forwardCylinder Z₀ R hR))) (χ : PDE.ScalarField d) (hs : tsupport χ ⊆ PDE.euclideanBall 0 (R ^ 3)) (f : HypoellipticAleksandrov.KineticScalarField d) (hf : Continuous f) (hz : ∀ Q, relativePosition Z₀ Q ∉ tsupport χ → f Q = 0)

include ha hT hu hs hf hz
/-- A continuous multiplier supported inside the position face preserves closed-strip continuity. -/
theorem localRepresentation_supported_mul_continuousOn   :
    ContinuousOn (fun Q => f Q * u Q) (localClosedStrip a T Z₀.velocity R) := by
  have hrel : Continuous (relativePosition Z₀) :=
    (continuous_position.sub continuous_const).sub
      ((continuous_time.sub continuous_const).smul continuous_const)
  intro P hP
  by_cases hx : relativePosition Z₀ P ∈ tsupport χ
  ·
    have hmem : closure (forwardCylinder Z₀ R hR) ∈
        𝓝[localClosedStrip a T Z₀.velocity R] P := by
      have hpos := hrel.continuousAt.preimage_mem_nhds
        ((PDE.isOpen_euclideanBall 0 (R ^ 3)).mem_nhds (hs hx))
      apply mem_of_superset (inter_mem (mem_nhdsWithin_of_mem_nhds hpos)
        self_mem_nhdsWithin)
      intro Q hQ
      exact local_closed_strip_mem_outer Z₀ Q hR ha hT hQ.2 hQ.1
    exact hf.continuousAt.continuousWithinAt.mul
      ((hu P (local_closed_strip_mem_outer Z₀ P hR ha hT hP (hs hx))).mono_of_mem_nhdsWithin hmem)
  ·
    exact (continuousAt_const.congr_of_eventuallyEq (by
        have hmem := hrel.continuousAt.preimage_mem_nhds
          ((isClosed_tsupport χ).isOpen_compl.mem_nhds hx)
        filter_upwards [hmem] with Q hQ
        rw [hz Q hQ, zero_mul])).continuousWithinAt

/-- Compact outer-cylinder data bound every position-supported strip multiplier. -/
theorem localRepresentation_supported_mul_bounded   :
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
theorem localRepresentation_indicator_measurable  (a T : ℝ)
    (v₀ : PDE.Vec d) (R : ℝ) (F : HypoellipticAleksandrov.KineticScalarField d)
    (hF : ContinuousOn F (localStrip a T v₀ R)) :
    Measurable ((localStrip a T v₀ R).indicator F) := by
  classical
  exact hF.measurable_piecewise continuousOn_const (measurableSet_localStrip a T v₀ R)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
