module

public import NearlyMinimax.PilotKernelEnergy


@[expose] public section

/-! Actual masked bilinear kernels inherit joint L² integrability from pilot
second moments and a weighted response-operator second moment. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace NearlyMinimax.PilotFields
set_option backward.isDefEq.respectTransparency false

variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {μ : Measure Ω} {ν : Measure W} [IsProbabilityMeasure μ] [SFinite ν]

def maskedPilotKernel (c : Ω → W → H) (A : W → H →L[ℝ] H)
    (q : W → ℝ) (z : (Ω × Ω) × W) : ℝ :=
  q z.2 * ⟪c z.1.1 z.2, A z.2 (c z.1.2 z.2)⟫

section
variable {c : Ω → W → H}

section
variable (hmc : Measurable (fun z : Ω × W => c z.1 z.2))
    {A : W → H →L[ℝ] H} (hmA : Measurable (fun z : W × H => A z.1 z.2))
    {q : W → ℝ} (hmq : Measurable q)
include hmc hmA hmq

theorem maskedPilotKernel_measurable : Measurable (maskedPilotKernel c A q) := by
  fun_prop [PilotFields.maskedPilotKernel]

/-- The pilot section estimates are needed only on the support of the mask. -/
theorem maskedPilotKernel_energy_facts (hq : ∀ w, q w ^ 2 = q w)
    (hA : Integrable (fun w => q w * ‖A w‖ ^ 2) ν)
    (hc : ∀ᵐ w ∂ν, q w ≠ 0 → MemLp (fun x => c x w) 2 μ)
    {L : ℝ} (hE : ∀ᵐ w ∂ν, q w ≠ 0 → (∫ x, ‖c x w‖ ^ 2 ∂μ) ≤ L) :
    MemLp (maskedPilotKernel c A q) 2 ((μ.prod μ).prod ν) ∧
    (∫ z, maskedPilotKernel c A q z ^ 2 ∂(μ.prod μ).prod ν) ≤
      L ^ 2 * ∫ w, q w * ‖A w‖ ^ 2 ∂ν := by
  have hm := (maskedPilotKernel_measurable hmc hmA hmq).aestronglyMeasurable (μ := (μ.prod μ).prod ν)
  obtain ⟨hi, hb⟩ := integrable_prod_and_integral_le (hm.pow 2) (hA.const_mul (L^2)) (by
    filter_upwards [hc, hE] with w hc hE
    by_cases hw : q w = 0
    · simp [maskedPilotKernel, hw]
    have hq0 : 0 ≤ q w := (hq w).symm ▸ sq_nonneg (q w)
    obtain ⟨hi, hb⟩ := product_operator_kernel_moments (A w) (hc hw)
    simp only [Pi.pow_apply, maskedPilotKernel, mul_pow, hq]
    refine ⟨hi.const_mul _, fun _ => mul_nonneg hq0 (sq_nonneg _), ?_⟩
    rw [integral_const_mul]
    calc
      _ ≤ q w * (‖A w‖ ^ 2 * L ^ 2) :=
        mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (integral_nonneg fun _ => sq_nonneg _) (hE hw) 2) (sq_nonneg _))) hq0
      _ = _ := by ring)
  exact ⟨(memLp_two_iff_integrable_sq hm).2 hi, by rwa [integral_const_mul] at hb⟩

end

end
end NearlyMinimax.PilotFields
