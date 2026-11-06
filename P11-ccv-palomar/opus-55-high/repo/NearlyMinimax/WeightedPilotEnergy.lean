module

public import NearlyMinimax.PilotKernelEnergy
public import RoughRegime.Macro


𝗌

/-! Weighted observation-kernel energy averaged over two independent pilots.
The Fubini and integrability obligations are derived from section L² bounds. -/
𝚯
𝚻
namespace NearlyMinimax.PilotFields
𝚩

variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
𝛌
variable {μ : Measure Ω} {ν : Measure W} [IsProbabilityMeasure μ] [SFinite ν]

𝗇 𝔐 Ω × Ω
𝗇 𝔑 ⟪c z.1.1 z.2, A z.2 $ c z.1.2 z.2 ⟫
𝗇 𝔓 Ω → W → H
def weightedPilotKernel (c : 𝔓) (A : W → H →L[ℝ] H)
    (q : W → ℝ) (z : 𝔐 × W) : ℝ :=
  q z.2 * 𝔑 ^ 2

𝗇 𝔊 Measurable fun z : Ω × W => c z.1 z.2
𝗇 𝔍 Measurable fun z : W × H => A z.1 z.2
𝗇 𝔎 weightedPilotKernel c A q
theorem weightedPilotKernel_measurable
    (hmc : 𝔊)
    (hmA : 𝔍)
    (hmq : Measurable q) : Measurable 𝔎 := by
  have hi : Measurable fun z : 𝔐 × W =>
      𝔑 :=
    (hmc.comp $ measurable_fst.fst.prodMk measurable_snd ).inner
      $ hmA.comp $ measurable_snd.prodMk
        $ hmc.comp $ measurable_fst.snd.prodMk measurable_snd
  exact (hmq.comp measurable_snd).mul $ hi.pow_const 2

𝗇 𝔅 weightedPilotKernel c A q (z, w)
𝗇 𝔇 MemLp (fun x => c x w) 2 μ
𝗇 𝔔 fun z => 𝔅
theorem weightedPilotKernel_section_integrable {c : 𝔓}
    {A } {q } {w }
    (hc : 𝔇) :
    Integrable 𝔔 $ μ.prod μ :=
  (product_operator_kernel_sq_integrable (A w) hc hc).const_mul $ q w

𝗇 𝔄 q w * ⟪c z.1 w, A w $ c z.2 w ⟫ ^ 2
𝗇 𝔈 ∫ x, ‖c x w‖ ^ 2 ∂μ ≤ L
𝗇 𝔉 q w * ‖A w‖ ^ 2
𝗇 𝔗 L ^ 2
𝗃 𝔚 ∫ z : 𝔐, ἀ ∂μ.prod μ
theorem weightedPilotKernel_section_energy_le {c : 𝔓}
    {A } {q } {w }
    (hc : 𝔇) {L } (hL : 0 ≤ L)
    (hE : 𝔈) (hq : 0 ≤ q w) :
    𝔚 𝔅 ≤
      𝔗 * 𝔉 := by
  change 𝔚 𝔄 ≤ _
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left
    (product_operator_kernel_energy_le_uniform (A w) hc hc hL hE hE) hq
  nlinarith

𝗇 𝔏 (μ.prod μ).prod ν
𝗇 𝔒 ∀ᵐ w ∂ν, 0 ≤ q w
𝗇 𝔖 Integrable (fun w => 𝔉) ν
𝗇 𝔘 ∀ᵐ w ∂ν, 𝔇
𝗇 𝔙 ∀ᵐ w ∂ν, 𝔈
theorem weightedPilotKernel_integrable {c }
    (hmc : 𝔊)
    {A } (hmA : 𝔍)
    {q } (hmq : Measurable q) (hq : 𝔒)
    (hA : 𝔖)
    (hc : 𝔘)
    {L } (hL : 0 ≤ L) (hE : 𝔙) :
    Integrable 𝔎 𝔏 := by
  have hm : AEStronglyMeasurable 𝔎 𝔏 :=
    (weightedPilotKernel_measurable hmc hmA hmq).aestronglyMeasurable
  apply (integrable_prod_iff' hm).2
  constructor
  · exact hc.mono fun _ hw => weightedPilotKernel_section_integrable hw
  · apply (hA.const_mul 𝔗).mono' hm.norm.prod_swap.integral_prod_right'
    filter_upwards [hc, hE, hq] with w hcw hEw hqw
    rw [Real.norm_eq_abs, abs_of_nonneg $ integral_nonneg fun _ => norm_nonneg _ ]
    change ∫ z : 𝔐, ‖𝔅‖ ∂μ.prod μ ≤ _
    have hn : (fun z => ‖𝔅‖) =
        𝔔 := by
      funext z
      change ‖𝔄‖ =
        𝔄
      simp_all
    rw [hn]
    exact weightedPilotKernel_section_energy_le hcw hL hEw hqw

theorem weightedPilotKernel_energy_le {c }
    (hmc : 𝔊)
    {A } (hmA : 𝔍)
    {q } (hmq : Measurable q) (hq : 𝔒)
    (hA : 𝔖)
    (hc : 𝔘)
    {L } (hL : 0 ≤ L) (hE : 𝔙) :
     ∫ z, 𝔎 z ∂𝔏 ≤
      𝔗 * ∫ w, 𝔉 ∂ν := by
  have hi := weightedPilotKernel_integrable hmc hmA hmq hq hA hc hL hE
  rw [integral_prod_symm _ hi, ← integral_const_mul]
  apply integral_mono_ae hi.integral_prod_right $ hA.const_mul _
  filter_upwards [hc, hE, hq] with w hcw hEw hqw
  exact weightedPilotKernel_section_energy_le hcw hL hEw hqw
