module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTestClosed

/-! # Actual uniform-in-spacetime bounds for a physical clock test -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution

/-- The genuine clock potential and its literal physical source are bounded on the active strip. -/
theorem ClockSourcePotentialSpec.pullback_bounded
    {lam Lam : ℝ} {A : SmoothAutonomous lam Lam} {c : Clock} {e : Point}
    {R T : ℝ} {f : exitProbeSubmodule} (h : ClockSourcePotentialSpec A c e R T f) :
    ∃ M : ℝ, ∀ p, p.velocity 0 ∈ c.active →
      |((clockSourcePotential A c e T f ∘ sectionTwoPoint) ∘
        c.map e) p| ≤ M ∧
      |forwardScalarOperator A.a
        ((clockSourcePotential A c e T f ∘ sectionTwoPoint) ∘
          c.map e) p| ≤ M := by
  obtain ⟨C, -, hb⟩ := h.bounded
  obtain ⟨M, hM⟩ := exitProbePhysical_bounded_source A f
  let D := |c.vbar| * c.r ^ 2
  have hD : 0 < D := mul_pos (abs_pos.mpr c.nonzero) (sq_pos_of_pos c.positive)
  refine ⟨max C ((3 * |c.vbar| / 2 / D) * max M 0), ?_⟩
  intro p hp
  refine ⟨(hb _).trans (le_max_left _ _), ?_⟩
  rw [h.physical_equation p hp, abs_mul, abs_neg,
    abs_of_nonneg (div_nonneg (abs_nonneg _) hD.le)]
  apply le_trans _ (le_max_right _ _)
  apply mul_le_mul
  · exact div_le_div_of_nonneg_right (c.active_abs_bounds hp).2 hD.le
  · exact (hM _).1.trans (le_max_left _ _)
  · exact abs_nonneg _
  · exact div_nonneg (by positivity) hD.le

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
