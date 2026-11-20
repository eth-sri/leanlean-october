module

public import NearlyMinimax.PilotFields


@[expose] public section

/-! Uniform section bounds imply genuine joint pilot L² integrability. -/
noncomputable section
open MeasureTheory
namespace NearlyMinimax.PilotFields
set_option backward.isDefEq.respectTransparency false

variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {μ : Measure Ω} {M : Measure W} [IsProbabilityMeasure μ] [IsFiniteMeasure M]

section
variable {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : ∀ᵐ w ∂M, MemLp (fun x => η x w) 2 μ)
    {R : ℝ} (hE : ∀ᵐ w ∂M, (∫ x, ‖η x w‖ ^ 2 ∂μ) ≤ R)
include hmη hη hE

theorem pilot_joint_section_moments :
    MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M) ∧
    (∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M) ≤ R * M.real Set.univ := by
  obtain ⟨hi, he⟩ := integrable_prod_and_integral_le (hmη.aestronglyMeasurable.norm.pow 2)
    (integrable_const R) (by
      filter_upwards [hη, hE] with w hw hE
      exact ⟨hw.norm.integrable_sq, fun _ => sq_nonneg _, hE⟩)
  exact ⟨(memLp_two_iff_integrable_sq_norm hmη.aestronglyMeasurable).2 hi,
    by simpa [integral_const, mul_comm] using he⟩

end
end NearlyMinimax.PilotFields
