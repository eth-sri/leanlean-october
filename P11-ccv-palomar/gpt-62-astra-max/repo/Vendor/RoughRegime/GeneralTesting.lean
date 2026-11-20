module

public import Mathlib
public import RoughRegime.Applications

@[expose] public section

/-!
# Testing for actual measures given by densities

Normalized real densities define probability measures. A pointwise square-root
comparison gives a two-point test-error bound on arbitrary measurable spaces.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace RoughRegime.GeneralTesting

/-- A normalized nonnegative integrable density on an arbitrary base measure. -/
structure DensityLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) where
  density : Ω → ℝ
  measurable : Measurable density
  integrable : Integrable density μ
  nonneg : 0 ≤ᵐ[μ] density
  integral_one : (∫ x, density x ∂μ) = 1

namespace DensityLaw

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

variable (L : DensityLaw μ) (A : Set Ω)

/-- The actual measure induced by the density. -/
def measure : Measure Ω :=
  μ.withDensity (fun x => ENNReal.ofReal (L.density x))

instance isProbabilityMeasure : IsProbabilityMeasure L.measure where
  measure_univ := by
    rw [measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal L.integrable L.nonneg, L.integral_one]
    exact ENNReal.ofReal_one

theorem measureReal_eq_setIntegral (hA : MeasurableSet A) :
    L.measure.real A = ∫ x in A, L.density x ∂μ := by
  rw [measureReal_def, measure, withDensity_apply _ hA]
  exact (integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae L.nonneg)
    L.integrable.integrableOn.aestronglyMeasurable).symm

theorem measureReal_eq_integral_indicator
    (hA : MeasurableSet A) :
    L.measure.real A = ∫ x, A.indicator L.density x ∂μ := by
  rw [integral_indicator hA]
  exact measureReal_eq_setIntegral L A hA

end DensityLaw

/-- Squared Hellinger distance in the convention without a factor of 1/2. -/
def hellingerSquared {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (L R : DensityLaw μ) : ℝ :=
  ∫ x, (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2 ∂μ

section
variable {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
include ha hb

/-- The square-root discrepancy is bounded by the sum of the densities. -/
theorem sqrt_difference_sq_le_add :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ a + b := by
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- A rational Young inequality convenient for two-point testing. -/
theorem square_root_testing_lower :
    3 * (a + b) / 8 - (Real.sqrt a - Real.sqrt b) ^ 2 ≤ min a b := by
  apply le_min
  · nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
      sq_nonneg (8 * Real.sqrt a - 5 * Real.sqrt b), sq_nonneg (Real.sqrt a)]
  · nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
      sq_nonneg (5 * Real.sqrt a - 8 * Real.sqrt b), sq_nonneg (Real.sqrt b)]

end

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {L R : DensityLaw μ} (ν : Measure Ω) {g : Ω → ℝ}
    (hg : Measurable g) (a b : ℝ)

theorem hellinger_integrable
    (L R : DensityLaw μ) :
    Integrable (fun x => (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2) μ := by
  refine (L.integrable.add R.integrable).mono'
    ((L.measurable.sqrt.sub R.measurable.sqrt).pow_const 2).aestronglyMeasurable ?_
  filter_upwards [L.nonneg, R.nonneg] with x hx hy
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sqrt_difference_sq_le_add hx hy

/-- Every measurable test has total error at least 3/4 minus squared Hellinger distance. -/
theorem test_loss_lower
    (L R : DensityLaw μ) {A : Set Ω} (hA : MeasurableSet A) :
    3 / 4 - hellingerSquared L R ≤ L.measure.real Aᶜ + R.measure.real A := by
  have hH := hellinger_integrable L R
  have hL := L.integrable.indicator hA.compl
  have hR := R.integrable.indicator hA
  have hp : (fun x => (3 / 8) * (L.density x + R.density x) -
      (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2) ≤ᵐ[μ]
      (fun x => Aᶜ.indicator L.density x + A.indicator R.density x) := by
    filter_upwards [L.nonneg, R.nonneg] with x hx hy
    have hl := square_root_testing_lower hx hy
    by_cases h : x ∈ A
    · rw [indicator_of_notMem (show x ∉ Aᶜ from fun hxA => hxA h),
        indicator_of_mem h, zero_add]
      grind
    · rw [indicator_of_mem (show x ∈ Aᶜ from h), indicator_of_notMem h, add_zero]
      grind
  have hi := integral_mono_ae
    (((L.integrable.add R.integrable).const_mul (3 / 8)).sub hH)
    (hL.add hR) hp
  change (∫ x, (3 / 8) * (L.density x + R.density x) -
    (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2 ∂μ) ≤
    ∫ x, Aᶜ.indicator L.density x + A.indicator R.density x ∂μ at hi
  have hI : Integrable (fun x => (3 / 8) * (L.density x + R.density x)) μ :=
    (L.integrable.add R.integrable).const_mul _
  rw [integral_sub hI hH,
    integral_const_mul, integral_add L.integrable R.integrable,
    L.integral_one, R.integral_one, integral_add hL hR,
    ← L.measureReal_eq_integral_indicator Aᶜ hA.compl,
    ← R.measureReal_eq_integral_indicator A hA] at hi
  unfold hellingerSquared
  linarith

/-- The two-point testing conclusion needed at squared Hellinger distance 1/4. -/
theorem test_loss_ge_half {A : Set Ω} (hA : MeasurableSet A)
    (hH : hellingerSquared L R ≤ 1 / 4) :
    1 / 2 ≤ L.measure.real Aᶜ + R.measure.real A := by
  bound [test_loss_lower L R hA]

include hg in
/-- At least one of two separated target values has absolute-error probability
at least one quarter under every measurable estimator. -/
theorem two_point_absolute_large_error
    (hH : hellingerSquared L R ≤ 1 / 4) :
    (1 / 4) ≤ L.measure.real {x | |b - a| / 2 ≤ |g x - a|} ∨
      (1 / 4) ≤ R.measure.real {x | |b - a| / 2 ≤ |g x - b|} := by
  let A  := {x | |g x - a| < |b - a| / 2}
  have hA : MeasurableSet A := measurableSet_lt (hg.sub measurable_const).abs measurable_const
  have he : Aᶜ = {x | |b - a| / 2 ≤ |g x - a|} := by
    ext x
    aesop
  have hsubset : A ⊆ {x | |b - a| / 2 ≤ |g x - b|} := by
    intro x hx
    have htri : |b - a| ≤ |g x - a| + |g x - b| := by
      simpa [abs_sub_comm, add_comm] using abs_sub_le b (g x) a
    grind
  have htest := test_loss_ge_half hA hH
  have hm := measureReal_mono (μ := R.measure) hsubset
  grind

include hg in
/-- A quarter-probability error at radius δ/2 forces L² error at least δ/4.
No finite-moment assumption is needed. -/
theorem tail_to_eLpNorm (target δ : ℝ)
    (hδ : 0 ≤ δ)
    (htail : (1 / 4) ≤ ν {x | δ / 2 ≤ |g x - target|}) :
    ENNReal.ofReal (δ / 4) ≤ eLpNorm (fun x => g x - target) 2 ν := by
  have hs := Applications.square_tail_lower ν (fun x => g x - target)
    (hg.sub measurable_const) (δ / 2) (by positivity)
  have hm : ENNReal.ofReal ((δ / 4) ^ 2) ≤
      ∫⁻ x, ENNReal.ofReal ((g x - target) ^ 2) ∂ν := by
    calc
      _ = ENNReal.ofReal ((δ / 2) ^ 2) * (1 / 4) := by
        calc
          _ = ENNReal.ofReal ((δ / 2) ^ 2 * (1 / 4)) := by ring
          _ = _ :=
            ENNReal.ofReal_mul (sq_nonneg _)
          _ = _ := by
            simp
      _ ≤ _ :=
        by gcongr
      _ ≤ _ := hs
  rw [Applications.eLpNorm_two_eq_squaredIntegral ν (fun x => g x - target) (hg.sub measurable_const)]
  have hh := (ENNReal.le_rpow_inv_iff
    (x := ENNReal.ofReal (δ / 4))
    (y := ∫⁻ x, ENNReal.ofReal ((g x - target) ^ 2) ∂ν)
    (by norm_num : (0 : ℝ) < 2)).2
  simpa using hh (by
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity) 2]
    exact hm)

include hg in
/-- The corresponding two-point L² lower bound for arbitrary measurable estimators. -/
theorem two_point_rmse_lower
    (hH : hellingerSquared L R ≤ 1 / 4) :
    ENNReal.ofReal (|b - a| / 4) ≤ eLpNorm (fun x => g x - a) 2 L.measure ∨
      ENNReal.ofReal (|b - a| / 4) ≤ eLpNorm (fun x => g x - b) 2 R.measure := by
  rcases two_point_absolute_large_error hg a b hH with h | h
  · exact Or.inl (by apply tail_to_eLpNorm L.measure hg a (|b - a|) (abs_nonneg _); have h := ENNReal.ofReal_le_of_le_toReal h; simpa using h)
  · exact Or.inr (by apply tail_to_eLpNorm R.measure hg b (|b - a|) (abs_nonneg _); have h := ENNReal.ofReal_le_of_le_toReal h; simpa using h)

end RoughRegime.GeneralTesting
