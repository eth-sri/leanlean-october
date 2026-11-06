/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Coupling.RadialTiltDensity
public import DOZZ.Brownian.Coupling.GaussianRadius
public import DOZZ.Brownian.Lateral.BrownianWindowExponential
public import DOZZ.Brownian.WienerExists
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Exponential moments of the conditioned entrance path

One-time exponential moments of the negative conditioned entrance law decay like `t^{-3/2}`
uniformly in the drift (Maxwell envelope of the entrance density) and exponentially at positive
drift. Unit-window increments have exponential moments of every order, uniformly over bounded
drifts, through the Rogers–Pitman realization on the Wiener triple. These are the radial inputs
of the block arguments for the reflection-mass moments and their zero-drift limit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- Every value of a negative conditioned path is nonpositive, almost surely and simultaneously
for all times. -/
theorem isNegativeConditionedBrownianLaw_ae_nonpos {ν : ℝ} {Q : Measure BrownianPath}
    (hQ : IsNegativeConditionedBrownianLaw ν Q) : ∀ᵐ p ∂Q, ∀ t : ℝ≥0, p t ≤ 0 := by
  rw [negativeConditionedBrownianLaw_eq_wiener ν hQ, negativeRogersPitmanWienerMeasure,
    negativeRogersPitmanEntranceMeasure]
  have hclosed : IsClosed {p : BrownianPath | ∀ t : ℝ≥0, p t ≤ 0} := by
    have h : {p : BrownianPath | ∀ t : ℝ≥0, p t ≤ 0} =
        ⋂ t : ℝ≥0, {p : BrownianPath | p t ≤ 0} := by
      aesop
    rw [h]
    exact isClosed_iInter fun t =>
      isClosed_le (continuous_eval_const t) continuous_const
  rw [ae_map_iff (measurable_negativeRogersPitmanPath ν).aemeasurable hclosed.measurableSet]
  refine ae_of_all _ fun V t => ?_
  simpa [negativeRogersPitmanPath] using (rogersPitmanPath_nonneg ν V t)

/-- The elementary bound `sinh x ≤ x e^x`. -/
theorem entranceExp_sinh_le_mul_exp (x : ℝ) : Real.sinh x ≤ x * Real.exp x := by
  have h1 := Real.one_sub_le_exp_neg (2 * x)
  have h2 : Real.exp (-x) = Real.exp x * Real.exp (-(2 * x)) := by
    rw [← Real.exp_add]
    ring_nf
  have h3 : Real.exp x * (1 - Real.exp (-(2 * x))) ≤ Real.exp x * (2 * x) :=
    by bound
  rw [Real.sinh_eq, h2]
  linarith
section
variable (ν t y : ℝ)

/-- The entrance density has a Gaussian envelope centred at the drifted position. -/
theorem conditionedPositiveEntranceDensity_le_gaussian (hν : 0 ≤ ν) (ht : 0 < t)
    (hy : 0 ≤ y) :
    conditionedPositiveEntranceDensity ν t y ≤
      Real.sqrt (2 / Real.pi) * t ^ (-(3 / 2 : ℝ)) * y ^ 2 *
        Real.exp (-(y - ν * t) ^ 2 / (2 * t)) := by
  rcases hy.eq_or_lt with rfl | hy'
  · simp [conditionedPositiveEntranceDensity]
  · have hK : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
    have hT : 0 < t ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos ht _
    unfold conditionedPositiveEntranceDensity
    simp only [hν, ht, hy', and_self, ite_true]
    rcases hν.eq_or_lt with rfl | hν'
    · simp only [ite_true, zero_mul, sub_zero]
      rw [Real.rpow_neg ht.le]
      grind
    · simp only [hν'.ne', ite_false]
      have hsinh : Real.sinh (ν * y) / ν ≤ y * Real.exp (ν * y) := by
        rw [div_le_iff₀ hν']
        calc Real.sinh _ ≤ (ν * y) * Real.exp _ := entranceExp_sinh_le_mul_exp _
          _ = y * Real.exp _ * ν := by ring
      have hexp : Real.exp (ν * y) * Real.exp (-y ^ 2 / (2 * t) - ν ^ 2 * t / 2) =
          Real.exp (-(y - ν * t) ^ 2 / (2 * t)) := by
        rw [← Real.exp_add]
        grind
      generalize Real.sqrt _ = K at *
      generalize t ^ (-(3 / 2 : ℝ)) = T at *
      have hE : 0 ≤ Real.exp (-y ^ 2 / (2 * t) - ν ^ 2 * t / 2) := Real.exp_nonneg _
      calc K * T * (y * Real.sinh _ / ν) * Real.exp _
          = K * T * y * (Real.sinh _ / ν) *
              Real.exp _ := by ring
        _ ≤ K * T * y * (y * Real.exp _) *
              Real.exp (-y ^ 2 / (2 * t) - ν ^ 2 * t / 2) := by
          bound
        _ = K * T * y ^ 2 *
              (Real.exp _ * Real.exp (-y ^ 2 / (2 * t) - ν ^ 2 * t / 2)) := by
          ring
        _ = K * T * y ^ 2 * Real.exp (-(y - ν * t) ^ 2 / (2 * t)) := by simp_all

/-- Maxwell envelope of the entrance density, uniform in the drift. -/
theorem conditionedPositiveEntranceDensity_le_maxwell (ht : 0 < t) :
    conditionedPositiveEntranceDensity ν t y ≤
      Real.sqrt (2 / Real.pi) * t ^ (-(3 / 2 : ℝ)) * y ^ 2 := by
  have hK : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
  have hT : 0 < t ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos ht _
  by_cases h : 0 ≤ ν ∧ 0 < y
  · have hg := conditionedPositiveEntranceDensity_le_gaussian ν t y h.1 ht h.2.le
    have hexp : Real.exp (-(y - ν * t) ^ 2 / (2 * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ (y - ν * t) ^ 2 / (2 * t) := by positivity
      grind
    calc _ ≤ _ := hg
      _ ≤ Real.sqrt _ * t ^ (-(3 / 2)) * y ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := mul_one _
  · have h0 : conditionedPositiveEntranceDensity ν t y = 0 := by
      unfold conditionedPositiveEntranceDensity
      simp_all
    rw [h0]
    positivity

end
section
variable {b : ℝ}
section
variable (hb : 0 < b)
include hb

/-- The Gamma integral `∫_0^∞ y² e^{-b y} dy = 2 / b³`, as a Bochner integral. -/
theorem entranceExp_integral_sq_mul_exp_neg :
    ∫ y in Ioi (0 : ℝ), y ^ 2 * Real.exp (-(b * y)) = 2 / b ^ 3 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (r := b) (by norm_num) hb
  have hΓ : Real.Gamma 3 = 2 := by
    simp
  rw [hΓ] at h
  have hpow : (1 / b) ^ (3 : ℝ) = 1 / b ^ 3 := by
    simp
  rw [hpow] at h
  rw [show 2 / b ^ 3 = 1 / b ^ 3 * 2 by ring, ← h]
  norm_num

/-- The Gamma integral `∫_0^∞ y² e^{-b y} dy = 2 / b³` as a lower integral. -/
theorem entranceExp_lintegral_sq_mul_exp_neg :
    (∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ 2 * Real.exp (-(b * y)))) =
      ENNReal.ofReal (2 / b ^ 3) := by
  have hint : IntegrableOn (fun y => y ^ 2 * Real.exp (-(b * y))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 2) (b := b)
      (by norm_num) one_pos hb
    simp_all
  rw [← entranceExp_integral_sq_mul_exp_neg hb,
    ← ofReal_integral_eq_lintegral_ofReal hint]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  positivity

end

end
section
variable {ν a : ℝ}

/-- The exponential moment of a negative conditioned path is an integral against the entrance
density over the positive half-line. -/
theorem entranceExp_lintegral_eq_entrance {Q : Measure BrownianPath} (hQ : IsNegativeConditionedBrownianLaw ν Q)
    (t : ℝ≥0) (ht : 0 < t) :
    (∫⁻ p, ENNReal.ofReal (Real.exp (a * p t)) ∂Q) =
      ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal
        (Real.exp (-(a * y)) * conditionedPositiveEntranceDensity ν (t : ℝ) y) := by
  rw [negativeConditionedBrownianLaw_eq_wiener ν hQ,
    negativeRogersPitmanWienerMeasure_lintegral_eval ν hQ.1 t ht
      (fun x => ENNReal.ofReal (Real.exp (a * x))) (by fun_prop),
    ← lintegral_entranceDensity_Ioi]
  refine setLIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  rw [ENNReal.ofReal_mul (Real.exp_nonneg _)]
  simp

/-- One-time exponential moment of the negative conditioned path: decay `t^{-3/2}`, uniformly in
the drift. -/
theorem isNegativeConditionedBrownianLaw_exp_eval_le (ha : 0 < a)
    {Q : Measure BrownianPath} (hQ : IsNegativeConditionedBrownianLaw ν Q)
    (t : ℝ≥0) (ht : 0 < t) :
    (∫⁻ p, ENNReal.ofReal (Real.exp (a * p t)) ∂Q) ≤
      ENNReal.ofReal (Real.sqrt (2 / Real.pi) * (2 / a ^ 3) * (t : ℝ) ^ (-(3 / 2 : ℝ))) := by
  have htr : (0 : ℝ) < t := ht
  have hK : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
  have hT : 0 < (t : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos htr _
  rw [entranceExp_lintegral_eq_entrance hQ t ht]
  calc _ ≤ ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal
        (Real.sqrt _ * (t : ℝ) ^ (-(3 / 2 : ℝ)) * (y ^ 2 * Real.exp _)) := by
        refine setLIntegral_mono' measurableSet_Ioi fun y _ => ?_
        apply ENNReal.ofReal_le_ofReal
        calc _ ≤ Real.exp _ *
              (Real.sqrt _ * (t : ℝ) ^ (-(3 / 2 : ℝ)) * y ^ 2) :=
            mul_le_mul_of_nonneg_left
              (conditionedPositiveEntranceDensity_le_maxwell ν t y htr) (Real.exp_nonneg _)
          _ = _ := by ring
    _ = ENNReal.ofReal (Real.sqrt (2 / Real.pi) * (t : ℝ) ^ (-(3 / 2 : ℝ))) *
        ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ 2 * Real.exp (-(a * y))) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        simp_all
    _ = ENNReal.ofReal (Real.sqrt (2 / Real.pi) * (t : ℝ) ^ (-(3 / 2 : ℝ))) *
        ENNReal.ofReal (2 / a ^ 3) := by rw [entranceExp_lintegral_sq_mul_exp_neg ha]
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- The same moment never exceeds one. -/
theorem isNegativeConditionedBrownianLaw_exp_eval_le_one (ha : 0 ≤ a)
    {Q : Measure BrownianPath} (hQ : IsNegativeConditionedBrownianLaw ν Q) (t : ℝ≥0) :
    (∫⁻ p, ENNReal.ofReal (Real.exp (a * p t)) ∂Q) ≤ 1 := by
  have : IsProbabilityMeasure Q := hQ.2.1
  calc (∫⁻ p, ENNReal.ofReal _ ∂Q) ≤ ∫⁻ _, 1 ∂Q := by
        refine lintegral_mono_ae ?_
        filter_upwards [isNegativeConditionedBrownianLaw_ae_nonpos hQ] with p hp
        rw [ENNReal.ofReal_le_one, Real.exp_le_one_iff]
        exact mul_nonpos_of_nonneg_of_nonpos ha (hp t)
    _ = 1 := by simp

end
section
variable {ν a t y : ℝ}

/-- Below half the drifted position the weighted entrance density is exponentially small. -/
theorem entranceExp_mul_density_le_of_le_half (hν : 0 ≤ ν) (ha : 0 ≤ a)
    (ht : 1 ≤ t) (hy : 0 < y) (hyM : y ≤ ν * t / 2) :
    Real.exp (-(a * y)) * conditionedPositiveEntranceDensity ν t y ≤
      Real.sqrt (2 / Real.pi) * (ν * t / 2) ^ 2 * Real.exp (-(ν ^ 2 * t / 8)) := by
  have ht0 : 0 < t := by linarith
  have hK : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
  have hT0 : 0 ≤ t ^ (-(3 / 2 : ℝ)) := by positivity
  have h1 : Real.exp (-(a * y)) ≤ 1 :=
    by simp_all
  have h2 : t ^ (-(3 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht (by norm_num)
  have h3 : y ^ 2 ≤ (ν * t / 2) ^ 2 := by nlinarith
  have h4 : Real.exp (-(y - ν * t) ^ 2 / (2 * t)) ≤ Real.exp (-(ν ^ 2 * t / 8)) := by
    apply Real.exp_le_exp.mpr
    have hsq : (ν * t / 2) ^ 2 ≤ (y - ν * t) ^ 2 := by
      have hnt : 0 ≤ ν * t := mul_nonneg hν ht0.le
      have h : ν * t / 2 ≤ ν * t - y := by linarith
      calc (ν * t / 2) ^ 2 ≤ (ν * t - y) ^ 2 := pow_le_pow_left₀ (by positivity) h 2
        _ = (y - ν * t) ^ 2 := by ring
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    linarith only [hsq]
  have hB : 0 ≤ Real.sqrt (2 / Real.pi) * t ^ (-(3 / 2 : ℝ)) * y ^ 2 *
      Real.exp (-(y - ν * t) ^ 2 / (2 * t)) := by positivity
  calc Real.exp _ * conditionedPositiveEntranceDensity ν t y
      ≤ Real.exp _ * (Real.sqrt _ * t ^ (-(3 / 2 : ℝ)) * y ^ 2 *
        Real.exp _) := mul_le_mul_of_nonneg_left (conditionedPositiveEntranceDensity_le_gaussian ν t y hν ht0 hy.le) (Real.exp_nonneg _)
    _ ≤ 1 * (Real.sqrt _ * t ^ (-(3 / 2 : ℝ)) * y ^ 2 *
        Real.exp _) := mul_le_mul_of_nonneg_right h1 hB
    _ = Real.sqrt _ * t ^ (-(3 / 2 : ℝ)) * y ^ 2 *
        Real.exp _ := one_mul _
    _ ≤ Real.sqrt (2 / Real.pi) * 1 * (ν * t / 2) ^ 2 * Real.exp (-(ν ^ 2 * t / 8)) := by
        gcongr
    _ = _ := by ring

/-- Above half the drifted position the weighted entrance density has a Gamma-integrable bound
with an exponential prefactor. -/
theorem entranceExp_mul_density_le_of_ge_half (ha : 0 ≤ a)
    (ht : 1 ≤ t) (hy : 0 < y) (hyM : ν * t / 2 ≤ y) :
    Real.exp (-(a * y)) * conditionedPositiveEntranceDensity ν t y ≤
      Real.sqrt (2 / Real.pi) * Real.exp (-(a * ν * t / 4)) *
        (y ^ 2 * Real.exp (-((a / 2) * y))) := by
  have ht0 : 0 < t := by linarith
  have hK : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
  have h2 : t ^ (-(3 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht (by norm_num)
  have h1 : Real.exp (-(a * y)) ≤ Real.exp (-(a * ν * t / 4)) * Real.exp (-((a / 2) * y)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hD : Real.sqrt (2 / Real.pi) * t ^ (-(3 / 2 : ℝ)) * y ^ 2 ≤
      Real.sqrt (2 / Real.pi) * y ^ 2 := by
    bound
  calc Real.exp _ * conditionedPositiveEntranceDensity ν t y
      ≤ Real.exp _ * (Real.sqrt _ * y ^ 2) :=
        mul_le_mul_of_nonneg_left ((conditionedPositiveEntranceDensity_le_maxwell ν t y ht0).trans hD) (Real.exp_nonneg _)
    _ ≤ (Real.exp _ * Real.exp _) *
        (Real.sqrt (2 / Real.pi) * y ^ 2) := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = _ := by ring

end

/-- Splitting the entrance integral at half the drifted position bounds the exponential moment by a
polynomial-times-Gaussian term and an exponentially decaying Gamma term. -/
theorem entranceExp_exp_eval_le_split {ν a : ℝ} (hν : 0 < ν) (ha : 0 < a)
    {Q : Measure BrownianPath} (hQ : IsNegativeConditionedBrownianLaw ν Q) (t : ℝ≥0)
    (ht : 1 ≤ (t : ℝ)) :
    (∫⁻ p, ENNReal.ofReal (Real.exp (a * p t)) ∂Q) ≤
      ENNReal.ofReal (Real.sqrt (2 / Real.pi) * (ν * (t : ℝ) / 2) ^ 3 *
          Real.exp (-(ν ^ 2 * (t : ℝ) / 8))) +
        ENNReal.ofReal (Real.sqrt (2 / Real.pi) * Real.exp (-(a * ν * (t : ℝ) / 4)) *
          (16 / a ^ 3)) := by
  have htpos : 0 < t := by
    have h : (0 : ℝ) < t := by linarith
    exact_mod_cast h
  have hK : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
  have hMpos : 0 < ν * t / 2 := by positivity
  rw [entranceExp_lintegral_eq_entrance hQ t htpos,
    ← Ioc_union_Ioi_eq_Ioi hMpos.le,
    lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
  refine add_le_add ?_ ?_
  · calc _ ≤ ∫⁻ _ in Ioc 0 _, ENNReal.ofReal
          (Real.sqrt _ * (ν * t / 2) ^ 2 * Real.exp _) :=
        setLIntegral_mono' measurableSet_Ioc fun y hy =>
          ENNReal.ofReal_le_ofReal
            (entranceExp_mul_density_le_of_le_half hν.le ha.le ht hy.1 hy.2)
      _ = ENNReal.ofReal (Real.sqrt (2 / Real.pi) * (ν * t / 2) ^ 2 *
            Real.exp (-(ν ^ 2 * t / 8))) * ENNReal.ofReal (ν * t / 2) := by
        simp
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  · calc _ ≤ ∫⁻ y in Ioi _, ENNReal.ofReal
          (Real.sqrt _ * Real.exp _ *
            (y ^ 2 * Real.exp _)) :=
        setLIntegral_mono' measurableSet_Ioi fun y hy =>
          ENNReal.ofReal_le_ofReal
            (entranceExp_mul_density_le_of_ge_half ha.le ht (hMpos.trans hy) (le_of_lt hy))
      _ ≤ ∫⁻ y in Ioi 0, ENNReal.ofReal
          (Real.sqrt _ * Real.exp _ *
            (y ^ 2 * Real.exp _)) :=
        lintegral_mono_set (Ioi_subset_Ioi hMpos.le)
      _ = ENNReal.ofReal _ *
          ∫⁻ y in Ioi 0, ENNReal.ofReal (y ^ 2 * Real.exp (-((a / 2) * y))) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
        rw [ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal _ *
          ENNReal.ofReal (2 / (a / 2) ^ 3) := by
        rw [entranceExp_lintegral_sq_mul_exp_neg (by positivity)]
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- Cubic growth is absorbed by half of an exponential decay rate. -/
theorem entranceExp_cube_mul_exp_neg_le {ε n : ℝ} (hε : 0 < ε) (hn : 0 ≤ n) :
    n ^ 3 * Real.exp (-(2 * ε * n)) ≤ 6 / ε ^ 3 * Real.exp (-(ε * n)) := by
  have h := Real.pow_div_factorial_le_exp (ε * n) (by positivity) 3
  have h6 : (ε * n) ^ 3 ≤ 6 * Real.exp (ε * n) := by
    linarith
  have hsplit : Real.exp (-(2 * ε * n)) = Real.exp (-(ε * n)) * Real.exp (-(ε * n)) := by
    rw [← Real.exp_add]
    ring_nf
  have hmul : Real.exp (ε * n) * Real.exp (-(ε * n)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hE : 0 ≤ Real.exp (-(ε * n)) := Real.exp_nonneg _
  have h7 : ε ^ 3 * (n ^ 3 * Real.exp (-(ε * n))) ≤ 6 := by
    nlinarith
  have h8 : n ^ 3 * Real.exp (-(ε * n)) ≤ 6 / ε ^ 3 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  calc n ^ 3 * Real.exp _ = (n ^ 3 * Real.exp _) * Real.exp _ := by
        grind
    _ ≤ 6 / ε ^ 3 * Real.exp _ := mul_le_mul_of_nonneg_right h8 hE

/-- The two terms of the split bound are dominated by two exponentials, uniformly for drifts in
`[ν₁, ν₂]` and times `n ≥ 1`. -/
theorem entranceExp_split_terms_le {K ν₁ ν₂ ν a n ε ρ : ℝ} (hK : 0 ≤ K) (hν₁ : 0 < ν₁)
    (ha : 0 < a) (hε : ε = ν₁ ^ 2 / 16) (hρ : ρ = a * ν₁ / 4) (h1 : ν₁ ≤ ν) (h2 : ν ≤ ν₂)
    (hn : 1 ≤ n) :
    K * (ν * n / 2) ^ 3 * Real.exp (-(ν ^ 2 * n / 8)) +
        K * Real.exp (-(a * ν * n / 4)) * (16 / a ^ 3) ≤
      K * (|ν₂| / 2) ^ 3 * (6 / ε ^ 3) * Real.exp (-(ε * n)) +
        K * (16 / a ^ 3) * Real.exp (-(ρ * n)) := by
  have hν0 := lt_of_lt_of_le hν₁ h1
  have hn0 : 0 ≤ n := by linarith
  have hε0 : 0 < ε := by simp_all
  refine add_le_add ?_ ?_
  · have e1 : ν * n / 2 ≤ |ν₂| * n / 2 := by
      have h := h2.trans (le_abs_self ν₂)
      nlinarith
    have e2 := pow_le_pow_left₀ (by positivity) e1 3
    have e3 : Real.exp (-(ν ^ 2 * n / 8)) ≤ Real.exp (-(2 * ε * n)) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hν₁.le h1 2) hn0
      bound
    calc K * (ν * n / 2) ^ 3 * Real.exp _
        ≤ K * (|ν₂| * n / 2) ^ 3 * Real.exp (-(2 * ε * n)) := by gcongr
      _ = K * (|ν₂| / 2) ^ 3 * (n ^ 3 * Real.exp (-(2 * ε * n))) := by ring
      _ ≤ K * (|ν₂| / 2) ^ 3 * (6 / ε ^ 3 * Real.exp _) :=
        mul_le_mul_of_nonneg_left (entranceExp_cube_mul_exp_neg_le hε0 hn0) (by positivity)
      _ = _ := by ring
  · have e : Real.exp (-(a * ν * n / 4)) ≤ Real.exp (-(ρ * n)) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 ha.le) hn0
      rw [hρ]
      linarith
    calc K * Real.exp _ * (16 / a ^ 3)
        = K * (16 / a ^ 3) * Real.exp _ := by ring
      _ ≤ K * (16 / a ^ 3) * Real.exp _ := by gcongr

/-- At positive drift the moment decays exponentially along integer times, uniformly on a compact
drift range bounded away from zero. -/
theorem isNegativeConditionedBrownianLaw_exp_eval_le_exp {ν₁ ν₂ a : ℝ} (hν₁ : 0 < ν₁)
    (ha : 0 < a) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ ν : ℝ, ν₁ ≤ ν → ν ≤ ν₂ → ∀ Q : Measure BrownianPath,
      IsNegativeConditionedBrownianLaw ν Q → ∀ n : ℕ,
        (∫⁻ p, ENNReal.ofReal (Real.exp (a * p (n : ℝ≥0))) ∂Q) ≤
          ENNReal.ofReal (C * Real.exp (-c * (n : ℝ))) := by
  have hK : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
  obtain ⟨K, hKdef⟩ : ∃ K, K = Real.sqrt (2 / Real.pi) := ⟨_, rfl⟩
  rw [← hKdef] at hK
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = ν₁ ^ 2 / 16 := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = a * ν₁ / 4 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by simp_all
  have hρ0 : 0 < ρ := by simp_all
  have hCA : 0 ≤ K * (|ν₂| / 2) ^ 3 * (6 / ε ^ 3) := by positivity
  have hCB : 0 ≤ K * (16 / a ^ 3) := by positivity
  refine ⟨1 + K * (|ν₂| / 2) ^ 3 * (6 / ε ^ 3) + K * (16 / a ^ 3), min ε ρ, by positivity,
    lt_min hε0 hρ0, ?_⟩
  intro ν hν₁' hν₂' Q hQ n
  have hν0 : 0 < ν := lt_of_lt_of_le hν₁ hν₁'
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine (isNegativeConditionedBrownianLaw_exp_eval_le_one ha.le hQ _).trans ?_
    simp
    linarith
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsplit := entranceExp_exp_eval_le_split hν0 ha hQ (n : ℝ≥0) (by assumption)
    rw [NNReal.coe_natCast, ← hKdef] at hsplit
    refine hsplit.trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hn0 : (0 : ℝ) ≤ n := by linarith
    have e1 : Real.exp (-(ε * n)) ≤ Real.exp (-(min ε ρ * n)) :=
      by bound
    have e2 : Real.exp (-(ρ * n)) ≤ Real.exp (-(min ε ρ * n)) :=
      by bound
    have hE : 0 ≤ Real.exp (-(min ε ρ * n)) := Real.exp_nonneg _
    rw [neg_mul]
    calc _ ≤ _ := (entranceExp_split_terms_le hK hν₁ ha hε hρ hν₁' hν₂' hn1)
      _ ≤ K * (|ν₂| / 2) ^ 3 * (6 / ε ^ 3) * Real.exp _ +
          K * (16 / a ^ 3) * Real.exp _ := add_le_add
        (mul_le_mul_of_nonneg_left e1 hCA) (mul_le_mul_of_nonneg_left e2 hCB)
      _ ≤ _ := by linarith
section
variable (p : BrownianPath)

/-- The path value at any time of the unit window is bounded by the window norm. -/
theorem abs_apply_le_brownianUnitNorm {t : ℝ≥0} (ht : t ≤ 1) :
    |p t| ≤ brownianUnitNorm p := by
  exact (p.restrict (Icc 0 1)).norm_coe_le_norm ⟨t, zero_le, ht⟩

/-- A uniform bound on the absolute path values of the unit window bounds the window norm. -/
theorem brownianUnitNorm_le_of_forall_abs_le {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ t : ℝ≥0, t ≤ 1 → |p t| ≤ M) : brownianUnitNorm p ≤ M := by
  refine (ContinuousMap.norm_le _ hM).mpr fun t => ?_
  aesop

end

/-- The Euclidean norm is bounded by the sum of the absolute coordinates. -/
theorem euclideanSpace_norm_le_sum_abs {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    ‖x‖ ≤ ∑ i, |x i| := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  simpa only [Real.norm_eq_abs] using
    Finset.sum_sq_le_sq_sum_of_nonneg
      (fun _ _ => abs_nonneg _)
section
variable (ν : ℝ)
section
variable (V : BrownianTriple) (n u : ℝ≥0)

/-- The drifted first coordinate increment after time `n` is the shifted coordinate path plus the
linear drift. -/
theorem rogersPitmanVectorAt_shift_sub_apply_zero :
    (rogersPitmanVectorAt ν V (n + u) - rogersPitmanVectorAt ν V n) 0 =
      brownianShiftPath n (V 0) u + ν * (u : ℝ) := by
  simp [rogersPitmanVectorAt, brownianShiftPath]
  ring

/-- The undrifted coordinate increments after time `n` are the shifted coordinate paths. -/
theorem rogersPitmanVectorAt_shift_sub_apply_of_ne_zero {i : Fin 3} (hi : i ≠ 0) :
    (rogersPitmanVectorAt ν V (n + u) - rogersPitmanVectorAt ν V n) i =
      brownianShiftPath n (V i) u := by
  simp [rogersPitmanVectorAt, brownianShiftPath, hi]

/-- The shifted negative radial path has the radial oscillation as its absolute value. -/
theorem abs_brownianShiftPath_negativeRogersPitmanPath :
    |brownianShiftPath n (negativeRogersPitmanPath ν V) u| =
      |‖rogersPitmanVectorAt ν V (n + u)‖ - ‖rogersPitmanVectorAt ν V n‖| := by
  change |-‖rogersPitmanVectorAt ν V _‖ - -‖rogersPitmanVectorAt ν V n‖| = _
  grind

end

/-- Pathwise, the unit-window oscillation of the negative radial path after time `n` is bounded by
the drift plus the three coordinate oscillations over the same window. -/
theorem brownianUnitNorm_shift_negativeRogersPitmanPath_le (hν : 0 ≤ ν)
    (V : BrownianTriple) (n : ℝ≥0) :
    brownianUnitNorm (brownianShiftPath n (negativeRogersPitmanPath ν V)) ≤
      ν + ∑ i : Fin 3, brownianUnitNorm (brownianShiftPath n (V i)) := by
  refine brownianUnitNorm_le_of_forall_abs_le _
    (add_nonneg hν (Finset.sum_nonneg fun i _ => norm_nonneg _)) fun u hu => ?_
  rw [abs_brownianShiftPath_negativeRogersPitmanPath]
  refine (abs_norm_sub_norm_le ..).trans ((euclideanSpace_norm_le_sum_abs _).trans ?_)
  rw [Fin.sum_univ_three, Fin.sum_univ_three, rogersPitmanVectorAt_shift_sub_apply_zero,
    rogersPitmanVectorAt_shift_sub_apply_of_ne_zero ν V n u (by decide),
    rogersPitmanVectorAt_shift_sub_apply_of_ne_zero ν V n u (by decide)]
  have hu' : u ≤ 1 := by exact_mod_cast hu
  have hd : ν * (u : ℝ) ≤ ν := mul_le_of_le_one_right hν hu'
  have h0 := abs_apply_le_brownianUnitNorm (brownianShiftPath n (V 0)) hu
  have h1 := abs_apply_le_brownianUnitNorm (brownianShiftPath n (V 1)) hu
  have h2 := abs_apply_le_brownianUnitNorm (brownianShiftPath n (V 2)) hu
  have ha := abs_add_le (brownianShiftPath n (V 0) u) (ν * (u : ℝ))
  rw [abs_of_nonneg (mul_nonneg hν u.coe_nonneg)] at ha
  linarith

end

/-- Three-term AM--GM in the weak form `a b c ≤ a ^ 3 + b ^ 3 + c ^ 3` for nonnegative reals. -/
theorem mul_mul_le_pow_three_add {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * b * c ≤ a ^ 3 + b ^ 3 + c ^ 3 := by
  nlinarith [mul_nonneg (add_nonneg (add_nonneg ha hb) hc)
    (add_nonneg (add_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c))) (sq_nonneg (c - a))),
    mul_nonneg (mul_nonneg ha hb) hc]
section
variable (θ ν ν₀ : ℝ)
section
variable (hθ : 0 ≤ θ)
include hθ

/-- Three-term AM--GM turns the exponential of a drift plus three oscillations into the sum of the
three triple-order exponentials, without any independence between the oscillations. -/
theorem exp_mul_add_sum_fin_three_le (hν : ν ≤ ν₀)
    (x : Fin 3 → ℝ) :
    Real.exp (θ * (ν + ∑ i, x i)) ≤ Real.exp (θ * ν₀) * ∑ i, Real.exp (3 * θ * x i) := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  have hexp : ∀ y : ℝ, Real.exp (3 * θ * y) = Real.exp (θ * y) ^ 3 := fun y => by
    rw [← Real.exp_nat_mul]
    ring
  have he : Real.exp (θ * (ν + (x 0 + x 1 + x 2))) =
      Real.exp (θ * ν) * (Real.exp (θ * x 0) * Real.exp (θ * x 1) * Real.exp (θ * x 2)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    ring
  rw [hexp, hexp, hexp, he]
  exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hν hθ))
    (mul_mul_le_pow_three_add (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le)
    (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (Real.exp_pos _).le)
    (Real.exp_pos _).le

/-- Pathwise exponential bound for the unit-window oscillation of the negative radial path in terms
of the three coordinate oscillations at triple order. -/
theorem ofReal_exp_unitIncrement_negativeRogersPitmanPath_le (hν : 0 ≤ ν) (hνν₀ : ν ≤ ν₀) (V : BrownianTriple) (n : ℝ≥0) :
    ENNReal.ofReal (Real.exp (θ * brownianUnitNorm
        (brownianShiftPath n (negativeRogersPitmanPath ν V)))) ≤
      ENNReal.ofReal (Real.exp (θ * ν₀)) * ∑ i : Fin 3,
        ENNReal.ofReal (Real.exp (3 * θ * brownianUnitNorm (brownianShiftPath n (V i)))) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (Real.exp_pos _).le),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ((Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left
      (brownianUnitNorm_shift_negativeRogersPitmanPath_le ν hν V n) hθ)).trans ?_)
  exact exp_mul_add_sum_fin_three_le θ ν ν₀ hθ hνν₀ _

end

end
section
variable (θ : ℝ)

/-- The shifted unit-window exponential is a measurable function of the path. -/
theorem measurable_ofReal_exp_mul_brownianUnitNorm_shift (n : ℝ≥0) :
    Measurable (fun p : BrownianPath =>
      ENNReal.ofReal (Real.exp (θ * brownianUnitNorm (brownianShiftPath n p)))) := by
  have hs : Measurable (brownianShiftPath n) :=
    continuous_brownianShiftPath.measurable.comp (measurable_const.prodMk measurable_id)
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul (continuous_brownianUnitNorm.measurable.comp hs)))

/-- Each coordinate path of the Wiener triple has the Brownian unit-increment exponential moment
bound. -/
theorem lintegral_wienerTriple_coordinate_unitIncrement_le (hθ : 0 ≤ θ) (n : ℝ≥0)
    (i : Fin 3) :
    (∫⁻ V, ENNReal.ofReal (Real.exp (θ * brownianUnitNorm (brownianShiftPath n (V i))))
      ∂wienerTripleMeasure) ≤ brownianWindowExponentialConstant θ := by
  calc
    _ = ∫⁻ p, ENNReal.ofReal _
        ∂wienerTripleMeasure.map (fun V => V i) :=
      (lintegral_map (measurable_ofReal_exp_mul_brownianUnitNorm_shift θ n) (measurable_pi_apply i)).symm
    _ = ∫⁻ p, ENNReal.ofReal _
        ∂wienerPathMeasure := by rw [(wienerTriple_coordinatePath_hasLaw i).map_eq]
    _ ≤ _ := brownianUnitIncrement_exponential_moment_le wienerPathMeasure
      wienerPathMeasure_isBrownian n θ hθ

end

/-- After any deterministic time, the unit-window oscillation of a negative conditioned entrance
path has exponential moments of every order, uniformly over bounded drifts. -/
theorem isNegativeConditionedBrownianLaw_unitIncrement_exp_le (θ ν₀ : ℝ) (hθ : 0 ≤ θ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ν : ℝ, ν ≤ ν₀ → ∀ Q : Measure BrownianPath,
      IsNegativeConditionedBrownianLaw ν Q → ∀ n : ℝ≥0,
        (∫⁻ p, ENNReal.ofReal (Real.exp (θ * brownianUnitNorm (brownianShiftPath n p))) ∂Q) ≤ C := by
  refine ⟨ENNReal.ofReal (Real.exp (θ * ν₀)) *
    (3 * brownianWindowExponentialConstant (3 * θ)), ?_, ?_⟩
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top (by norm_num) (brownianWindowExponentialConstant_lt_top _))
  · intro ν hν Q hQ n
    have hQeq : Q = wienerTripleMeasure.map (negativeRogersPitmanPath ν) :=
      negativeConditionedBrownianLaw_eq_wiener ν hQ
    rw [hQeq, lintegral_map (measurable_ofReal_exp_mul_brownianUnitNorm_shift θ n)
      (measurable_negativeRogersPitmanPath ν)]
    calc
      _ ≤ ∫⁻ V, ENNReal.ofReal (Real.exp (θ * ν₀)) * ∑ i : Fin 3,
          ENNReal.ofReal (Real.exp (3 * θ * brownianUnitNorm (brownianShiftPath n (V i))))
          ∂wienerTripleMeasure :=
        lintegral_mono fun V =>
          ofReal_exp_unitIncrement_negativeRogersPitmanPath_le θ ν ν₀ hθ hQ.1 hν V n
      _ = ENNReal.ofReal _ * ∑ i : Fin 3,
          ∫⁻ V, ENNReal.ofReal
            (Real.exp _)
            ∂wienerTripleMeasure := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_finsetSum _ fun i _ =>
          (measurable_ofReal_exp_mul_brownianUnitNorm_shift _ n).comp
            (measurable_pi_apply i)
      _ ≤ ENNReal.ofReal _ *
          ∑ i : Fin 3, brownianWindowExponentialConstant _ := by
        gcongr with i
        exact lintegral_wienerTriple_coordinate_unitIncrement_le _
          (mul_nonneg (by norm_num) hθ) n i
      _ = _ := by simp

end DOZZ.Proofs

end
