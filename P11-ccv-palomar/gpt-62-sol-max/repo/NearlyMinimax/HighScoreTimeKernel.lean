module

public import NearlyMinimax.HighTimeMarginal


@[expose] public section

/-! The energy path is measurable on a fixed reference, with the same density
used to differentiate the observed-data mean. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
variable {J : Type*} [Fintype J] [LinearOrder J]

/-- Joint Borel dependence and a genuine energy bound imply the square-root
energy is interval integrable. -/
theorem intervalIntegrable_sqrt_of_measurable_bound (f : ℝ → ℝ)
    (hf : Measurable f) (T M : ℝ) (hT : 0 ≤ T)
    (hbound : ∀ t ∈ Icc 0 T, f t ≤ M) :
    IntervalIntegrable (fun t => Real.sqrt (f t)) volume 0 T := by
  apply (intervalIntegrable_const (c := Real.sqrt M)).mono_fun'
    (Real.continuous_sqrt.measurable.comp hf).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [uIoc_of_le hT] at ht
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using Real.sqrt_le_sqrt (hbound t ⟨ht.1.le, ht.2⟩)

section
variable {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] {d : ℕ}
    {dependent : J → J → Prop} {Δ : ℕ} {π : Measure E} [IsProbabilityMeasure π]
    {activation : E → ℝ} {T Ba : ℝ} (P : HistoryPriorBounds dependent Δ π activation T Ba)
    (n : ℕ) (a v η aRaw bRaw : ℝ) (ha : 0 < a) (haRaw : 0 < aRaw) (hT : 0 ≤ T)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ t ∈ Icc 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v-η^2*t) y)

local notation "ν" => (fun t => historyMarkedPrior dependent Δ t π activation)
local notation "V" => (fun t => v-η^2*t)
local notation "data" => (fun t => highDataLaw (ν t) n a (V t) p F hp hF)
local notation "score" => (fun t => highMarginalRealScore dependent P.symm (ν t) π activation n a (V t) η p F)
local notation "energy" => (fun t => ∫ z, (score t z)^2 ∂data t)

include aRaw bRaw ha haRaw hraw hq hT in
theorem highHistoryScore_sqrt_energy_intervalIntegrable (M : ℝ)
    (hbound : ∀ t ∈ Icc 0 T, energy t ≤ M) :
    IntervalIntegrable (fun t => Real.sqrt (energy t)) volume 0 T := by
  let _ := P.reference_probability
  let L (t : ℝ) := highMarginalRawLikelihood (ν t) n a (V t) p F
  let S (t : ℝ) := highMarginalIndexScore dependent P.symm (ν t) π activation n a (V t) η p F
  let Z (t : ℝ) := massPowerNormalizer (ν t) (fun ω => highRawDensityMass (p ω)) n
  let W (t : ℝ) := (∫ z, L t z * (S t z)^2 ∂highSampleReference d n) / Z t
  have hL := highMarginalRawLikelihood_time_measurable dependent Δ π activation P.measurable n a v η p F hp hF
  have hS := highMarginalIndexScore_time_measurable dependent P.symm Δ π activation P.measurable n a v η p F hp hF
  have hZ := highMassPowerNormalizer_time_measurable dependent Δ π activation P.measurable n p hp
  have hW : Measurable W := (hL.mul (hS.pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable.div hZ
  have he (t : ℝ) (ht : t ∈ Icc 0 T) : energy t = W t := by
    let _ := P.probability ht
    have hm := (highMarginalRealScore_measurable dependent P.symm (ν t) π activation P.measurable
      n a (V t) η p F hp hF).pow_const 2
    dsimp only
    rw [highDataLaw_integral_marginal (ν t) n a (V t) p F hp hF aRaw bRaw haRaw ha.ne' hraw (hq t ht) _ hm]
    simp only [W, L, S, Z, highMarginalRealScore_encode _ _ _ _ _ ha]
  apply (intervalIntegrable_sqrt_of_measurable_bound W hW T M hT
    (fun t ht => he t ht ▸ hbound t ht)).congr
  intro t ht
  rw [uIoc_of_le hT] at ht
  exact congrArg Real.sqrt (he t ⟨ht.1.le, ht.2⟩).symm

end
end NearlyMinimax
