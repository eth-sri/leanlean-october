module

public import NearlyMinimax.FinePairActionEnvelopes
public import NearlyMinimax.FineFieldSumEnergy
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Genuine spatial energy of the higher even-field action. All moment
bounds here concern the actual time-integrated hyperplane field law. -/
𝚫
𝚪
𝚨
𝚩
𝚭
𝚬

 𝗇 𝔄 f i x
theorem finite_sum_abs_square_integrable [MeasurableSpace X]
    (μ : Measure X) (s : Finset I) (f : I → X → ℝ)
    (hm : ∀ i ∈ s, Measurable $ f i )
    (hi : ∀ i ∈ s, Integrable (fun x => 𝔄 ^ 2) μ) :
    Integrable (fun x => (∑ i ∈ s, |𝔄|)^2) μ := by
  have hupper : Integrable (fun x => s.card * ∑ i ∈ s, 𝔄 ^ 2) μ :=
    (integrable_finsetSum s hi).const_mul _
  apply hupper.mono' ((Finset.measurable_sum s fun i hi => (hm i hi).abs ).pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_sq]
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] using
      Finset.sum_mul_sq_le_sq_mul_sq s 𝙃 fun i => |𝔄|

 def finePairEvenActionSpatialBudget (d n M q : ℕ) (ad bd C a ρ η T0 : ℝ) : ℝ :=
  (𝗺₁ *
    (𝘁 * 𝙒^2 * 𝙎))^2 *
      fineFieldSubsetEnergyBase d ^ n * 𝙒^8 * (T0 ^ (2-𝙊))^2
