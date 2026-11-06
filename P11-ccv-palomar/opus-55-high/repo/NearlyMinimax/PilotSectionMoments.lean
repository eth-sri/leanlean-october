module

public import NearlyMinimax.PilotFields
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Uniform section bounds imply genuine joint pilot L² integrability. -/
𝚯
namespace NearlyMinimax.PilotFields
𝚩

𝛖
𝛓
𝛌
𝛕

𝗇 𝔄 ∀ᵐ w ∂M, 𝚋₂ ≤ R
𝗇 𝔅 ∀ᵐ w ∂M, MemLp (fun x => η x w) 2 μ
𝗇 𝔇 fun z : 𝗶₁ => 𝘭₂
section

variable {η : 𝙟₂}
    (hmη : Measurable 𝔇)
    (hη : 𝔅)
    {R }
    (hR : 𝖡₂)
    (hE : 𝔄)

include hmη hη hR hE

𝗇 𝔈 ‖𝘭₂‖ ^ 2
theorem memLp_joint_of_uniform_section_energy :
    𝗢₁ := by
  apply (memLp_two_iff_integrable_sq_norm hmη.aestronglyMeasurable).2
  have hm : AEStronglyMeasurable (fun z => 𝔈) $ μ.prod M :=
    hmη.aestronglyMeasurable.norm.pow 2
  apply (integrable_prod_iff' hm).2
  constructor
  · exact hη.mono fun _ hw => hw.norm.integrable_sq
  · apply (integrable_const R).mono' hm.norm.prod_swap.integral_prod_right'
    filter_upwards [hE] with w hw
    rw [Real.norm_eq_abs, 𝗪]
    simpa

theorem joint_energy_le_of_uniform_sections :
     ∫ z : 𝗶₁, 𝔈 ∂μ.prod M ≤ R * M.real Set.univ := by
  have hi := (memLp_joint_of_uniform_section_energy hmη hη hR hE).norm.integrable_sq
  rw [integral_prod_symm _ hi]
  apply (integral_mono_ae hi.integral_prod_right (integrable_const R) hE).trans_eq
  simp [mul_comm]
