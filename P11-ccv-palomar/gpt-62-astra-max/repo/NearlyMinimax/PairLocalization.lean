module

public import NearlyMinimax.PairUStatistic
public import NearlyMinimax.PilotFields


@[expose] public section

/-! Row localization for arbitrary unbounded same-cell pair kernels. -/
noncomputable section
open MeasureTheory Set
namespace NearlyMinimax.PairUStatistic
set_option backward.isDefEq.respectTransparency false

variable {E I : Type*} [MeasurableSpace E] [MeasurableSpace I]
variable [MeasurableSingletonClass I]
variable {μ : Measure E} [IsProbabilityMeasure μ]

variable {Ω : Type*} {label : E → I} (hlabel : Measurable label) {K : E × E → ℝ}
    (hK : MemLp K 2 (μ.prod μ)) (hsupport : ∀ x y, label x ≠ label y → K (x, y) = 0)

include hlabel hsupport in
theorem supported_row_sq_le
    {x : E} (hKx : MemLp (fun y => K (x, y)) 2 μ)
    {cap : ℝ} (hcap : ∀ i, μ.real (label ⁻¹' {i}) ≤ cap) :
    rowIntegral (μ := μ) K x ^ 2 ≤ cap * ∫ y, K (x, y) ^ 2 ∂μ := by
  let S := label ⁻¹' {label x}
  have hS : MeasurableSet S := (measurableSet_singleton _).preimage hlabel
  have he : S.indicator (fun y => K (x, y)) = (fun y => K (x, y)) := by
    funext y
    apply Set.indicator_apply_eq_self.mpr <;> grind
  have he₂ : S.indicator (fun y => K (x, y) ^ 2) = (fun y => K (x, y) ^ 2) := by
    simp_all
  have hrestrict : (μ.restrict S).real univ = μ.real S := by
    simp
  calc
    _ = _ := by
      rw [← integral_indicator hS, he]
      rfl
    _ ≤ _ :=
      LocalizationL2.integral_sq_le_mass_mul_integral_sq (hKx.restrict S)
    _ = _ := by
      rw [hrestrict, ← integral_indicator hS, he₂]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hcap (label x))
      (by positivity)

include hlabel hK hsupport in
theorem partition_row_energy_le
    {cap : ℝ} (hcap : ∀ i, μ.real (label ⁻¹' {i}) ≤ cap) :
    (∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ) ≤
      cap * ∫ z, K z ^ 2 ∂μ.prod μ := by
  have hsec : ∀ᵐ x ∂μ, MemLp (fun y => K (x, y)) 2 μ :=
    PilotFields.memLp_sections hK
  calc
    _ ≤ _ := by
      apply integral_mono_ae (rowIntegral_sq_integrable hK)
        (hK.integrable_sq.integral_prod_left.const_mul cap)
      filter_upwards [hsec] with x hx
      exact supported_row_sq_le hlabel hsupport hx hcap
    _ = _ := by rw [integral_const_mul, integral_prod _ hK.integrable_sq]

theorem partition_pairAverage_centered_sq_le [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {n : ℕ} (hn : 2 ≤ n)
    {X : Fin n → Ω → E} (hind : ProbabilityTheory.iIndepFun X ν)
    (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {label : E → I} (hlabel : Measurable label)
    {K : E × E → ℝ} (hmK : Measurable K) (hK : MemLp K 2 (μ.prod μ))
    (hsym : ∀ x y, K (x, y) = K (y, x))
    (hsupport : ∀ x y, label x ≠ label y → K (x, y) = 0)
    {cap : ℝ} (hcap : ∀ i, μ.real (label ⁻¹' {i}) ≤ cap) :
    (∫ x, (pairAverage n K (fun i => X i x) - ∫ z, K z ∂μ.prod μ) ^ 2 ∂ν) ≤
      (4 / n * cap + 2 / (n * (n - 1 : ℕ))) *
        ∫ z, K z ^ 2 ∂μ.prod μ := by
  apply (pairAverage_centered_sq_le hn hind hX hmK hK hsym).trans
  have he := mul_le_mul_of_nonneg_left
    (partition_row_energy_le hlabel hK hsupport hcap)
    (by positivity : 0 ≤ 4 / (n : ℝ))
  nlinarith

end NearlyMinimax.PairUStatistic
