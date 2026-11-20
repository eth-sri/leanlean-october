module

public import NearlyMinimax.PilotKernelEnergy


@[expose] public section

/-! Weighted observation-kernel energy averaged over two independent pilots.
The Fubini and integrability obligations are derived from section L² bounds. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace NearlyMinimax.PilotFields
set_option backward.isDefEq.respectTransparency false

variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {μ : Measure Ω} {ν : Measure W} [IsProbabilityMeasure μ] [SFinite ν]

def weightedPilotKernel (c : Ω → W → H) (A : W → H →L[ℝ] H)
    (q : W → ℝ) (z : (Ω × Ω) × W) : ℝ :=
  q z.2 * ⟪c z.1.1 z.2, A z.2 (c z.1.2 z.2)⟫ ^ 2

variable {c : Ω → W → H} (hmc : Measurable (fun z : Ω × W => c z.1 z.2)) {A : W → H →L[ℝ] H}
    (hmA : Measurable (fun z : W × H => A z.1 z.2)) {q : W → ℝ} (hmq : Measurable q)
    (hq : ∀ᵐ w ∂ν, 0 ≤ q w) (hA : Integrable (fun w => q w * ‖A w‖ ^ 2) ν)
    (hc : ∀ᵐ w ∂ν, MemLp (fun x => c x w) 2 μ) {L : ℝ} (hL : 0 ≤ L)
    (hE : ∀ᵐ w ∂ν, (∫ x, ‖c x w‖ ^ 2 ∂μ) ≤ L)

include hmc hmA hmq in
theorem weightedPilotKernel_measurable : Measurable (weightedPilotKernel c A q) := (hmq.comp measurable_snd).mul (((hmc.comp (measurable_fst.fst.prodMk measurable_snd)).inner (by fun_prop)).pow_const 2)

theorem weightedPilotKernel_section_energy_le {w : W}
    (hc : MemLp (fun x => c x w) 2 μ) {L : ℝ} (hL : 0 ≤ L)
    (hE : (∫ x, ‖c x w‖ ^ 2 ∂μ) ≤ L) (hq : 0 ≤ q w) :
    (∫ z, weightedPilotKernel c A q (z, w) ∂μ.prod μ) ≤
      L ^ 2 * (q w * ‖A w‖ ^ 2) := by
  change (∫ z, q w * ⟪c z.1 w, A w (c z.2 w)⟫ ^ 2 ∂μ.prod μ) ≤ _
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left
    (product_operator_kernel_energy_le_uniform (A w) hc hc hL hE hE) hq
  nlinarith

include hmc hmA hmq hq hA hc hL hE in
theorem weightedPilotKernel_integrable :
    Integrable (weightedPilotKernel c A q) ((μ.prod μ).prod ν) := by
  have hm : AEStronglyMeasurable (weightedPilotKernel c A q) ((μ.prod μ).prod ν) :=
    (weightedPilotKernel_measurable hmc hmA hmq).aestronglyMeasurable
  apply (integrable_prod_iff' hm).2
  constructor
  · exact hc.mono (fun _ hw => (product_operator_kernel_sq_integrable (A _) hw hw).const_mul (q _))
  · apply (hA.const_mul (L ^ 2)).mono' hm.norm.prod_swap.integral_prod_right'
    filter_upwards [hc, hE, hq] with w hcw hEw hqw
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    change (∫ z, ‖weightedPilotKernel c A q (z, w)‖ ∂μ.prod μ) ≤ _
    have hn : (fun z => ‖weightedPilotKernel c A q (z, w)‖) =
        (fun z => weightedPilotKernel c A q (z, w)) := by
      funext z
      change ‖q w * ⟪c z.1 w, A w (c z.2 w)⟫ ^ 2‖ =
        q w * _
      simp_all
    rw [hn]
    exact weightedPilotKernel_section_energy_le hcw hL hEw hqw

include hmc hmA hmq hq hA hc hL hE in
theorem weightedPilotKernel_energy_le :
    (∫ z, weightedPilotKernel c A q z ∂(μ.prod μ).prod ν) ≤
      L ^ 2 * ∫ w, q w * ‖A w‖ ^ 2 ∂ν := by
  have hi := weightedPilotKernel_integrable hmc hmA hmq hq hA hc hL hE
  rw [integral_prod_symm _ hi, ← integral_const_mul]
  apply integral_mono_ae hi.integral_prod_right (hA.const_mul _)
  filter_upwards [hc, hE, hq] with w hcw hEw hqw
  exact weightedPilotKernel_section_energy_le hcw hL hEw hqw

end NearlyMinimax.PilotFields
