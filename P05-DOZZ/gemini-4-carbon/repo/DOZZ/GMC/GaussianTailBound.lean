/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import DOZZ.GMC.FiniteGaussianTilt
public import DOZZ.GMC.FiniteChaosMean

/-! Exponential Markov bounds for centered one-dimensional Gaussian tails. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]


section
variable (v : ℝ≥0) (b : ℝ) (hv : 0 < v)
include b hv

/-- Chernoff's upper-tail bound for a centered Gaussian with positive variance. -/
theorem gaussianReal_upper_tail_bound (hb : 0 ≤ b) :
    gaussianReal 0 v (Set.Ioi b) ≤
      ENNReal.ofReal (Real.exp (-b ^ 2 / (2 * (v : ℝ)))) := by
  let s := b / (v : ℝ)
  have hs : 0 ≤ s := by positivity
  have hv0 : (v : ℝ) ≠ 0 := ne_of_gt hv
  refine (measure_mono fun x (hx : b < x) => (ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.le hs)) :
      ENNReal.ofReal (Real.exp (s * b)) ≤ ENNReal.ofReal (Real.exp (s * x)))).trans ?_
  refine (meas_ge_le_lintegral_div (by fun_prop) (by positivity) (by simp)).trans_eq ?_
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal s)
    (ae_of_all _ fun _ => (Real.exp_pos _).le)]
  have hmgf : (∫ x, Real.exp (s * x) ∂gaussianReal 0 v) = Real.exp ((v : ℝ) * s ^ 2 / 2) := by
    simpa [mgf] using congrFun (mgf_id_gaussianReal (μ := 0) (v := v)) s
  rw [hmgf, ← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
  congr 2; dsimp [s]; field_simp; ring

/-- Chernoff's lower-tail bound for a centered Gaussian; obtained by symmetry from the upper-tail
bound. -/
theorem gaussianReal_lower_tail_bound (hb : b ≤ 0) :
    gaussianReal 0 v (Set.Iio b) ≤
      ENNReal.ofReal (Real.exp (-b ^ 2 / (2 * (v : ℝ)))) := by
  have hmap : gaussianReal 0 v (Iio b) = gaussianReal 0 v (Ioi (-b)) := by
    rw [show Iio b = (fun x : ℝ => -x) ⁻¹' Ioi (-b) by ext; simp,
      ← Measure.map_apply (by fun_prop) measurableSet_Ioi, gaussianReal_map_neg, neg_zero]
  rw [hmap]
  simpa using gaussianReal_upper_tail_bound v (-b) hv (neg_nonneg.mpr hb)


end
section
variable (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : IsCenteredJointlyGaussian P Z) (tilt : ι → ℝ) (j : ι)
include hZ tilt j

private lemma tilt_coord_indicator_eq
 {s : Set ℝ} (hs : MeasurableSet s) :
    ∃ v : ℝ≥0, (v : ℝ) = gaussianVariance P (fun ω => Z ω j) ∧
      ∫⁻ ω, ENNReal.ofReal (Real.exp
          ((∑ k, tilt k * Z ω k) -
            (∑ k, ∑ l, tilt k * gaussianCovariance P
              (fun ω => Z ω k) (fun ω => Z ω l) * tilt l) / 2)) *
        {ω | Z ω j ∈ s}.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P =
      gaussianReal 0 v ((fun x => x + ∑ k, gaussianCovariance P
        (fun ω => Z ω j) (fun ω => Z ω k) * tilt k) ⁻¹' s) := by
  classical
  obtain ⟨v, hmap, _, hvar⟩ := coordinate_mean_variance P Z hZ j
  let m := ∑ k, gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω k) * tilt k
  let ev : (ι → ℝ) → ℝ≥0∞ := fun z => s.indicator 1 (z j)
  have hev : Measurable ev := (measurable_const.indicator hs).comp (measurable_pi_apply j)
  refine ⟨v, hvar.symm, ?_⟩
  have ht := finite_gaussian_tilt P Z hZ tilt ev hev
  refine (lintegral_congr_ae (ae_of_all _ fun ω => ?_)).trans (ht.trans ?_)
  · simp [ev, indicator]
  · have hZi := hZ.2.1 j
    have hs' : MeasurableSet ((fun x => x + m) ⁻¹' s) := hs.preimage (by fun_prop)
    rw [show (fun ω => ev fun k => Z ω k + ∑ l, gaussianCovariance P (fun ω => Z ω k)
        (fun ω => Z ω l) * tilt l) = ((fun ω => Z ω j) ⁻¹' ((fun x => x + m) ⁻¹' s)).indicator 1
        by ext ω; simp [ev, m, indicator],
      lintegral_indicator_one₀ (hZi.nullMeasurableSet_preimage hs'),
      ← Measure.map_apply_of_aemeasurable hZi hs', hmap]

/-- A finite Wick tilt shifts a Gaussian barrier coordinate by the covariance pairing; the
barrier-violation expectation is bounded by the Gaussian Chernoff tail of that shifted coordinate.
This form includes the two-root tilt used in the mixed-cutoff GMC kernel. -/
theorem finite_gaussian_tilt_barrier_tail_bound

 (b : ℝ)
    (hgap : ∑ k, gaussianCovariance P (fun ω => Z ω j)
      (fun ω => Z ω k) * tilt k < b)
    (hv : 0 < gaussianVariance P (fun ω => Z ω j)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp
        ((∑ k, tilt k * Z ω k) -
          (∑ k, ∑ l, tilt k * gaussianCovariance P
            (fun ω => Z ω k) (fun ω => Z ω l) * tilt l) / 2)) *
      (Set.indicator {ω | b < Z ω j} (fun _ => (1 : ℝ≥0∞)) ω) ∂P ≤
        ENNReal.ofReal (Real.exp
          (-(b - ∑ k, gaussianCovariance P (fun ω => Z ω j)
              (fun ω => Z ω k) * tilt k) ^ 2 /
            (2 * gaussianVariance P (fun ω => Z ω j)))) := by
  obtain ⟨v, hv_eq, hI⟩ := tilt_coord_indicator_eq P Z hZ tilt j (s := Ioi b) measurableSet_Ioi
  let m := ∑ k, gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω k) * tilt k
  have hv' : 0 < v := by exact_mod_cast hv_eq.symm ▸ hv
  refine hI.trans_le ?_
  rw [show ((fun x => x + m) ⁻¹' Ioi b) = Ioi (b - m) by ext; simp [sub_lt_iff_lt_add']]
  simpa [hv_eq, m] using gaussianReal_upper_tail_bound v (b - m) hv' (sub_nonneg.mpr hgap.le)


end

/-- The finite Gaussian tilt corresponding to two equal-charge roots. -/
def twoRootTilt {ι : Type*} [DecidableEq ι]
    (root₁ root₂ : ι) (g : ℝ) : ι → ℝ :=
  fun i => if i = root₁ then g else if i = root₂ then g else 0

private lemma sum_twoRootTilt_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {root₁ root₂ : ι} (h₁₂ : root₁ ≠ root₂) (g : ℝ) (f : ι → ℝ) :
    ∑ i, twoRootTilt root₁ root₂ g i * f i = g * f root₁ + g * f root₂ := by
  have hc (i : ι) : twoRootTilt root₁ root₂ g i =
      (if i = root₁ then g else 0) + (if i = root₂ then g else 0) := by
    unfold twoRootTilt; split_ifs <;> simp_all
  simp [hc, add_mul, Finset.sum_add_distrib, ite_mul]

/-- The Wick product of two root exponentials is the common two-root Gaussian tilt density,
multiplied by the deterministic exponential of the cross covariance. -/
theorem finite_gaussian_two_root_wick_tilt_integral_identity
 [DecidableEq ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (root₁ root₂ : ι) (h₁₂ : root₁ ≠ root₂) (g : ℝ)
    (B : Ω → ℝ≥0∞) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp
        (g * Z ω root₁ - g ^ 2 / 2 * gaussianVariance P
            (fun ω => Z ω root₁))) *
      ENNReal.ofReal (Real.exp
        (g * Z ω root₂ - g ^ 2 / 2 * gaussianVariance P
            (fun ω => Z ω root₂))) * B ω ∂P =
      ENNReal.ofReal (Real.exp (g ^ 2 * gaussianCovariance P
        (fun ω => Z ω root₁) (fun ω => Z ω root₂))) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp
          ((∑ i, twoRootTilt root₁ root₂ g i * Z ω i) -
            (∑ i, ∑ j, twoRootTilt root₁ root₂ g i *
              gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) *
              twoRootTilt root₁ root₂ g j) / 2)) * B ω ∂P := by
  have hcovsym : gaussianCovariance P (fun ω => Z ω root₂) (fun ω => Z ω root₁) =
      gaussianCovariance P (fun ω => Z ω root₁) (fun ω => Z ω root₂) := by
    simp only [gaussianCovariance, mul_comm]
  rw [← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_congr_ae (ae_of_all _ fun ω => ?_)
  dsimp only
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, ← mul_assoc
    (ENNReal.ofReal _), ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 3
  simp only [sum_twoRootTilt_mul h₁₂, mul_comm (_ : ℝ) (twoRootTilt _ _ _ _)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_twoRootTilt_mul h₁₂,
    gaussianVariance, hcovsym]
  ring



/-- Once the barrier slope exceeds the tilted mean slope, Gaussian tails decay exponentially
uniformly when the variance is at most linear in the scale. -/
theorem gaussian_barrier_tail_rate
    (a g C m v k : ℝ)
    (hgap : g < a) (hk : 0 < k)
    (hC : C ≤ (a - g) * k / 2)
    (hmean : m ≤ g * k + C)
    (hv : 0 < v) (hvUpper : v ≤ 2 * k) :
    Real.exp (-((a * k - m) ^ 2) / (2 * v)) ≤
      Real.exp (-((a - g) ^ 2 * k / 16)) := by
  rw [neg_div]
  refine Real.exp_le_exp.mpr (neg_le_neg ((le_div_iff₀ (by positivity)).2 ?_))
  have h1 : ((a - g) ^ 2 * k / 16) * (2 * v) ≤ ((a - g) * k / 2) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hvUpper (by positivity : 0 ≤ (a - g) ^ 2 * k)]
  exact h1.trans (pow_le_pow_left₀ (by positivity) (by linarith) 2)

/-- A one-root Wick tilt has an exponentially small coarse-scale barrier tail when the tilted
mean and variance differ from their linear scale asymptotics by a bounded amount. This is the
uniform estimate used for the discarded mass in the good/bad circle construction. -/
theorem finite_gaussian_tilt_coarse_barrier_tail_rate

    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : IsCenteredJointlyGaussian P Z) (fine coarse : ι)
    (k g a C : ℝ) (hg : 0 < g) (hga : g < a) (hk : 0 < k)
    (hCk : C < k)
    (hvar : |gaussianVariance P (fun ω => Z ω coarse) - k| ≤ C)
    (hcov : |gaussianCovariance P (fun ω => Z ω coarse)
      (fun ω => Z ω fine) - k| ≤ C)
    (hgapScale : g * C ≤ (a - g) * k / 2) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp
        (g * Z ω fine - g ^ 2 / 2 * gaussianVariance P (fun ω => Z ω fine))) *
      (Set.indicator {ω | a * k < Z ω coarse}
        (fun _ => (1 : ℝ≥0∞)) ω) ∂P ≤
      ENNReal.ofReal (Real.exp (-((a - g) ^ 2 * k / 16))) := by
  have finite_gaussian_tilt_coordinate_tail_bound (i j : ι) (γ b : ℝ) (hgap : γ * gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω i) < b) (hv : 0 < gaussianVariance P (fun ω => Z ω j)) : ∫⁻ ω, ENNReal.ofReal (Real.exp
          (γ * Z ω i - γ ^ 2 / 2 * gaussianVariance P (fun ω => Z ω i))) *
        (Set.indicator {ω | b < Z ω j} (fun _ => (1 : ℝ≥0∞)) ω) ∂P ≤
          ENNReal.ofReal (Real.exp
            (-(b - γ * gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω i)) ^ 2 /
              (2 * gaussianVariance P (fun ω => Z ω j)))) := by
    classical
    have h := finite_gaussian_tilt_barrier_tail_bound P Z hZ (fun k => if k = i then γ else 0) j b
      (by simpa [mul_ite, mul_comm] using hgap) hv
    simpa [ite_mul, mul_ite, gaussianVariance, mul_comm, sq, div_eq_mul_inv, mul_left_comm, mul_assoc] using h
  obtain ⟨hv1, hv2⟩ := abs_le.mp hvar
  obtain ⟨hc1, hc2⟩ := abs_le.mp hcov
  have hvPos : 0 < gaussianVariance P (fun ω => Z ω coarse) := by linarith
  refine (finite_gaussian_tilt_coordinate_tail_bound fine coarse g (a * k)
    (by nlinarith) hvPos).trans (ENNReal.ofReal_le_ofReal ?_)
  simpa [neg_div] using gaussian_barrier_tail_rate a g (g * C) _ _ k hga hk hgapScale (by nlinarith) hvPos (by linarith)

/-- The exponential barrier tail appearing in the good/bad construction is summable in the
integer scale whenever its rate is positive. -/
theorem summable_gaussian_barrier_tail (c : ℝ) (hc : 0 < c) :
    Summable (fun k : ℕ => Real.exp (-c * (k : ℝ))) := by
  simpa only [neg_mul, mul_comm c, ← mul_neg, Real.exp_nat_mul] using
    summable_geometric_of_lt_one (Real.exp_nonneg (-c)) (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc))


/-- A pair of Wick roots restricted to the good coarse barrier has the expected spatial power
bound once the admissible covariance errors are small relative to scale. The two-root tilt tail
and the logarithmic cross-covariance estimate enter separately, matching the good-mass second
moment calculation. -/
theorem finite_gaussian_wick_pair_good_barrier_power_bound
 [DecidableEq ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : IsCenteredJointlyGaussian P Z)
    (root₁ root₂ coarse : ι) (h₁₂ : root₁ ≠ root₂)
    (g a C η k d ρ κ : ℝ)
    (hg : 0 < g) (hga : a < 2 * g) (hk : 0 < k)
    (hη : 0 < η) (hη1 : η < 1)
    (hCsmall : C ≤ η * k)
    (hoffset : 2 * g * C + 1 ≤ η * (2 * g - a) * k)
    (hvar : |gaussianVariance P (fun ω => Z ω coarse) - k| ≤ C)
    (hcov₁ : |gaussianCovariance P (fun ω => Z ω coarse)
      (fun ω => Z ω root₁) - k| ≤ C)
    (hcov₂ : |gaussianCovariance P (fun ω => Z ω coarse)
      (fun ω => Z ω root₂) - k| ≤ C)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hd : 0 < d) (hdρ : d ≤ ρ)
    (hcov : gaussianCovariance P (fun ω => Z ω root₁)
      (fun ω => Z ω root₂) ≤ Real.log (1 / ρ) + C)
    (hfloor : Real.log (1 / ρ) - 1 < k)
    (hκ : 0 ≤ κ)
    (hκrate : g ^ 2 -
      ((1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η))) ≤ κ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp
        (g * Z ω root₁ - g ^ 2 / 2 * gaussianVariance P
            (fun ω => Z ω root₁))) *
      ENNReal.ofReal (Real.exp
        (g * Z ω root₂ - g ^ 2 / 2 * gaussianVariance P
            (fun ω => Z ω root₂))) *
      Set.indicator {ω | Z ω coarse ≤ a * k} (fun _ => (1 : ℝ≥0∞)) ω ∂P ≤
      ENNReal.ofReal ((Real.exp (g ^ 2 * C +
        ((1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η)))) * d ^ (-κ))) := by
  have finite_gaussian_tilt_double_root_good_barrier_rate_of_small_error : ∫⁻ ω, ENNReal.ofReal (Real.exp
          ((∑ i, twoRootTilt root₁ root₂ g i * Z ω i) -
            (∑ i, ∑ j, twoRootTilt root₁ root₂ g i *
              gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) *
              twoRootTilt root₁ root₂ g j) / 2)) *
        (Set.indicator {ω | Z ω coarse ≤ a * k}
          (fun _ => (1 : ℝ≥0∞)) ω) ∂P ≤
        ENNReal.ofReal (Real.exp
          (-((1 - η) ^ 2 * (2 * g - a) ^ 2 * k / (2 * (1 + η))))) := by
    have finite_gaussian_tilt_barrier_lower_tail_bound (tilt : ι → ℝ) (j : ι) (b : ℝ) (hgap : b < ∑ k, gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω k) * tilt k) (hv : 0 < gaussianVariance P (fun ω => Z ω j)) : ∫⁻ ω, ENNReal.ofReal (Real.exp
            ((∑ k, tilt k * Z ω k) -
              (∑ k, ∑ l, tilt k * gaussianCovariance P
                (fun ω => Z ω k) (fun ω => Z ω l) * tilt l) / 2)) *
          (Set.indicator {ω | Z ω j < b} (fun _ => (1 : ℝ≥0∞)) ω) ∂P ≤
            ENNReal.ofReal (Real.exp
              (-((∑ k, gaussianCovariance P (fun ω => Z ω j)
                  (fun ω => Z ω k) * tilt k) - b) ^ 2 /
                (2 * gaussianVariance P (fun ω => Z ω j)))) := by
      obtain ⟨v, hv_eq, hI⟩ := tilt_coord_indicator_eq P Z hZ tilt j (s := Iio b) measurableSet_Iio
      let m := ∑ k, gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω k) * tilt k
      have hv' : 0 < v := by exact_mod_cast hv_eq.symm ▸ hv
      refine hI.trans_le ?_
      rw [show ((fun x => x + m) ⁻¹' Iio b) = Iio (b - m) by ext; simp [lt_sub_iff_add_lt']]
      refine (gaussianReal_lower_tail_bound v (b - m) hv' (sub_nonpos.mpr hgap.le)).trans_eq ?_
      rw [hv_eq]; dsimp [m]; congr 3; ring
    let m := ∑ i, gaussianCovariance P (fun ω => Z ω coarse) (fun ω => Z ω i) * twoRootTilt root₁ root₂ g i
    have hm : m = g * gaussianCovariance P (fun ω => Z ω coarse) (fun ω => Z ω root₁) +
        g * gaussianCovariance P (fun ω => Z ω coarse) (fun ω => Z ω root₂) := by
      simpa only [m, mul_comm _ (twoRootTilt _ _ _ _)] using sum_twoRootTilt_mul h₁₂ g _
    obtain ⟨hv_lo, hv_hi⟩ := abs_le.mp hvar
    have hc1 := (abs_le.mp hcov₁).1
    have hc2 := (abs_le.mp hcov₂).1
    have hv : 0 < gaussianVariance P (fun ω => Z ω coarse) := by nlinarith
    have hgap : (1 - η) * (2 * g - a) * k ≤ m - (a * k + 1) := by nlinarith
    have hpos : 0 < (1 - η) * (2 * g - a) * k := by positivity
    have ht := finite_gaussian_tilt_barrier_lower_tail_bound (twoRootTilt root₁ root₂ g)
      coarse (a * k + 1) (by linarith) hv
    refine (lintegral_mono fun ω => mul_le_mul_of_nonneg_left ?_ bot_le).trans
      (ht.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)))
    · by_cases h : Z ω coarse ≤ a * k
      · have h' : Z ω coarse < a * k + 1 := by linarith
        simp [indicator, h, h']
      · simp [indicator, h]
    · rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
      calc ((1 - η) ^ 2 * (2 * g - a) ^ 2 * k / (2 * (1 + η))) * (2 * gaussianVariance P (fun ω => Z ω coarse))
          ≤ ((1 - η) ^ 2 * (2 * g - a) ^ 2 * k / (2 * (1 + η))) * (2 * ((1 + η) * k)) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = ((1 - η) * (2 * g - a) * k) ^ 2 := by field_simp
        _ ≤ (m - (a * k + 1)) ^ 2 := pow_le_pow_left₀ hpos.le hgap 2
  have good_barrier_kernel_power_bound_of_rate (θ κ C cov k d ρ : ℝ) (hθ : 0 ≤ θ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hd : 0 < d) (hdρ : d ≤ ρ) (hcov : cov ≤ Real.log (1 / ρ) + C) (hk : Real.log (1 / ρ) - 1 < k) (hκ : 0 ≤ κ) (hgap : g ^ 2 - θ ≤ κ) : Real.exp (g ^ 2 * cov) * Real.exp (-θ * k) ≤
        Real.exp (g ^ 2 * C + θ) * d ^ (-κ) := by
    rw [← Real.exp_add, Real.rpow_def_of_pos hd, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h1 := mul_le_mul_of_nonneg_right hgap (Real.log_nonneg ((one_le_div hρ).2 hρ1))
    have h2 := mul_le_mul_of_nonneg_left
      (Real.log_le_log (by positivity) (one_div_le_one_div_of_le hd hdρ)) hκ
    have h3 := mul_le_mul_of_nonneg_left hcov (sq_nonneg g)
    have h4 := mul_nonneg hθ (sub_nonneg.mpr hk.le)
    simp only [one_div, Real.log_inv] at h1 h2 h3 h4 ⊢
    linarith
  rw [finite_gaussian_two_root_wick_tilt_integral_identity P Z root₁ root₂ h₁₂ g]
  have htail := finite_gaussian_tilt_double_root_good_barrier_rate_of_small_error
  have hk' := good_barrier_kernel_power_bound_of_rate _ κ C _ k d ρ
    (by positivity) hρ hρ1 hd hdρ hcov hfloor hκ hκrate
  refine (mul_le_mul_right htail _).trans ?_
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), mul_div_right_comm (_ * _ : ℝ), ← neg_mul]
  exact ENNReal.ofReal_le_ofReal hk'

/-- A fixed subcritical charge admits a barrier slope whose two-root power is locally integrable.
This is the scalar parameter choice underlying the good-mass construction. -/
theorem exists_fixed_charge_barrier_parameters (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ a κ : ℝ, γ < a ∧ a < 2 * γ ∧
      κ = γ ^ 2 - (2 * γ - a) ^ 2 / 2 ∧ 0 < κ ∧ κ < 2 := by
  let δ := min (γ / 2) ((2 - γ ^ 2 / 2) / (2 * γ + 1))
  have hgap : 0 < 2 - γ ^ 2 / 2 := by nlinarith
  have : 0 < δ := lt_min (by positivity) (div_pos hgap (by positivity))
  have h1 : δ ≤ γ / 2 := min_le_left _ _
  have h2 : δ * (2 * γ + 1) ≤ 2 - γ ^ 2 / 2 := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  refine ⟨γ + δ, γ ^ 2 - (2 * γ - (γ + δ)) ^ 2 / 2, by linarith, by linarith, rfl,
    by nlinarith, by nlinarith [sq_nonneg δ]⟩

end DOZZ.Proofs
