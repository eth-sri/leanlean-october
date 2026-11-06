module

public import NearlyMinimax.WeightedPilotEnergy
public import RoughRegime.Macro


𝗌

/-! Actual masked bilinear kernels inherit joint L² integrability from pilot
second moments and a weighted response-operator second moment. -/
𝚯
𝚻
namespace NearlyMinimax.PilotFields
𝚩

variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
𝛌
variable {μ : Measure Ω} {ν : Measure W} [IsProbabilityMeasure μ] [SFinite ν]

def maskedPilotKernel (c : Ω → W → H) (A : W → H →L[ℝ] H)
    (q : W → ℝ) (z : (Ω × Ω) × W) : ℝ :=
  q z.2 * ⟪c z.1.1 z.2, A z.2 $ c z.1.2 z.2 ⟫

𝗇 𝔄 Measurable fun z : Ω × W => c z.1 z.2
𝗇 𝔅 Measurable fun z : W × H => A z.1 z.2
𝗇 𝔎 maskedPilotKernel c A q
theorem maskedPilotKernel_measurable
    (hmc : 𝔄)
    (hmA : 𝔅)
    (hmq : Measurable q) : Measurable 𝔎 := (hmq.comp measurable_snd).mul
    $ (hmc.comp $ measurable_fst.fst.prodMk measurable_snd ).inner
      $ hmA.comp $ measurable_snd.prodMk
        $ hmc.comp $ measurable_fst.snd.prodMk measurable_snd

𝗇 𝔉 ∀ w, q w ^ 2 = q w
theorem maskedPilotKernel_sq_eq {c : Ω → W → H} {A }
    {q } (hq : 𝔉) z :
    𝔎 z ^ 2 = weightedPilotKernel c A q z := by
  simp only [maskedPilotKernel, weightedPilotKernel, mul_pow, hq]

𝗇 𝔇 ∀ᵐ w ∂ν, ∫ x, ‖c x w‖ ^ 2 ∂μ ≤ L
𝗇 𝔈 Filter.Eventually.of_forall fun w => (hq w).symm ▸ sq_nonneg (q w)
𝗇 𝔊 q w * ‖A w‖ ^ 2
𝗇 𝔍 ∀ᵐ w ∂ν, MemLp (fun x => c x w) 2 μ
𝗇 𝔏 Integrable (fun w => 𝔊) ν
𝗇 𝔐 (μ.prod μ).prod ν
theorem maskedPilotKernel_memLp {c }
    (hmc : 𝔄)
    {A } (hmA : 𝔅)
    {q } (hmq : Measurable q) (hq : 𝔉)
    (hA : 𝔏)
    (hc : 𝔍)
    {L } (hL : 0 ≤ L) (hE : 𝔇) :
    MemLp 𝔎 2 𝔐 := by
  apply (memLp_two_iff_integrable_sq
    (maskedPilotKernel_measurable hmc hmA hmq).aestronglyMeasurable).2
  simp_rw [maskedPilotKernel_sq_eq hq]
  exact weightedPilotKernel_integrable hmc hmA hmq
    𝔈 hA hc hL hE

theorem maskedPilotKernel_energy_le {c }
    (hmc : 𝔄)
    {A } (hmA : 𝔅)
    {q } (hmq : Measurable q) (hq : 𝔉)
    (hA : 𝔏)
    (hc : 𝔍)
    {L } (hL : 0 ≤ L) (hE : 𝔇) :
     ∫ z, 𝔎 z ^ 2 ∂𝔐 ≤
      L ^ 2 * ∫ w, 𝔊 ∂ν := by
  simp_rw [maskedPilotKernel_sq_eq hq]
  exact weightedPilotKernel_energy_le hmc hmA hmq
    𝔈 hA hc hL hE
