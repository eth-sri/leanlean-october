module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.EulerMaclaurin
import WeylPort.Analytic.RealLaplace

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Assembly of the corrected weighted Poisson formula, Part I -/

namespace DhimanKadiriQuesadaHerrera2026

open MeasureTheory

/-- The finite endpoint expression obtained by integrating the stationary frequency head. -/
noncomputable def poissonHeadBoundary (f g : ℝ → ℝ) (x : ℝ) (M : ℕ) : ℂ :=
  weightedWave f g x / (2 * Real.pi * Complex.I) * finiteS1 x M

/-- The actual finite sum of Fourier integrals from zero through M. -/
noncomputable def poissonMain (f g : ℝ → ℝ) (a b : ℝ) (M : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 0 M, ∫ x in a..b, weightedWave f g x * expMode x n

/-- The actual negative Fourier mode has its stated derivative. -/
theorem hasDerivAt_expMode (n : ℕ) (x : ℝ) :
    HasDerivAt (fun u => expMode u n)
      ((-2 * Real.pi * Complex.I * n) * expMode x n) x := by
  have he : (fun u : ℝ => expMode u n) =
      fun u : ℝ => Complex.exp ((-2 * Real.pi * Complex.I * n) * (u : ℂ)) := by
    funext u
    unfold expMode
    congr 1
    push_cast
    ring
  rw [he]
  have ht := ((hasDerivAt_id x).ofReal_comp.const_mul
    (-2 * (Real.pi : ℂ) * Complex.I * n)).cexp
  rw [congrFun he x]
  simp only [id_eq, Complex.ofReal_one, mul_one] at ht
  convert ht using 1
  ring

section
variable {f g : ℝ → ℝ} {a b : ℝ} (h : PartIRegularity f g a b)
include f g a b h
/-- The regularity hypotheses provide the exact derivative of the source wave on the interval. -/
theorem PartIRegularity.wave_hasDerivAt (x : ℝ) (hx : x ∈ Set.uIcc a b) :
    HasDerivAt (weightedWave f g) (waveDerivative f g x) x := by
  rw [Set.uIcc_of_le h.lt.le] at hx
  unfold weightedWave waveDerivative
  simpa only [Complex.ofReal_mul, mul_assoc] using
    weighted_wave_hasDerivAt (h.f_differentiable x hx) (h.g_differentiable x hx)

/-- Integration by parts for one actual frequency in the finite head. -/
theorem negativeCoefficient_eq_boundary_add_integral {n : ℕ} (hn : 0 < n) :
    negativeCoefficient f g a b n =
      weightedWave f g b * expMode b n / (2 * Real.pi * Complex.I * n) -
      weightedWave f g a * expMode a n / (2 * Real.pi * Complex.I * n) +
        ∫ x in a..b, weightedWave f g x * expMode x n := by
  have hm : Continuous (fun x => (-2 * Real.pi * Complex.I * (n : ℂ)) * expMode x n) := by
    unfold expMode
    fun_prop
  have hi : IntervalIntegrable (waveDerivative f g) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h.lt.le]
    exact h.waveDerivative_continuous
  have hb := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => hasDerivAt_expMode n x) h.wave_hasDerivAt (hm.intervalIntegrable a b) hi
  have he1 : (fun x => expMode x n * waveDerivative f g x) =
      fun x => waveDerivative f g x * expMode x n := by funext x; ring
  have he2 : (fun x => (-2 * Real.pi * Complex.I * (n : ℂ) * expMode x n) * weightedWave f g x) =
      fun x => (-2 * Real.pi * Complex.I * (n : ℂ)) * (weightedWave f g x * expMode x n) := by
    funext x
    ring
  pm_958 he1 integral_waveDerivative_expMode he2 intervalIntegral.integral_const_mul hb
  unfold negativeCoefficient
  rw [hb]
  pm_146 hnc n hn.ne'
  pm_146 hπ Real.pi Real.pi_ne_zero
  field_simp
  ring
end

/-- The finite endpoint expression is exactly the sum of the endpoint Fourier coefficients. -/
theorem poissonHeadBoundary_eq_sum (f g : ℝ → ℝ) (x : ℝ) (M : ℕ) :
    poissonHeadBoundary f g x M =
      ∑ n ∈ Finset.Icc 1 M, weightedWave f g x * expMode x n / (2 * Real.pi * Complex.I * n) := by
  unfold poissonHeadBoundary finiteS1
  rw [Nat.floor_natCast, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- All finite-head integrations by parts assemble with their actual complex endpoint terms. -/
theorem sum_negativeCoefficient_head {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, negativeCoefficient f g a b n) =
      poissonHeadBoundary f g b M - poissonHeadBoundary f g a M +
        ∑ n ∈ Finset.Icc 1 M, ∫ x in a..b, weightedWave f g x * expMode x n := by
  rw [poissonHeadBoundary_eq_sum, poissonHeadBoundary_eq_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact negativeCoefficient_eq_boundary_add_integral h (by
    have := (Finset.mem_Icc.mp hn).1
    omega)

/-- Separating the zero frequency gives exactly the main integral plus the positive head. -/
theorem poissonMain_eq_zero_add_head (f g : ℝ → ℝ) (a b : ℝ) (M : ℕ) :
    poissonMain f g a b M = (∫ x in a..b, weightedWave f g x) +
      ∑ n ∈ Finset.Icc 1 M, ∫ x in a..b, weightedWave f g x * expMode x n := by
  pm_1125
  rw [poissonMain, hset, Finset.sum_range_succ', sum_Icc_one_eq_sum_range]
  simp only [expMode, Nat.cast_zero, mul_zero, zero_mul, Complex.ofReal_zero,
    Complex.exp_zero, mul_one]
  rw [add_comm]

section
variable {f g : ℝ → ℝ} {a b : ℝ} (h : PartIRegularity f g a b) (M : ℕ)
include f g a b h M
/-- Absolute convergence permits the exact finite-head and infinite-tail decomposition. -/
theorem negativeCoefficient_sum_eq_head_add_tail :
    (∑' n, negativeCoefficient f g a b n) =
      (∑ n ∈ Finset.Icc 1 M, negativeCoefficient f g a b n) +
        ∑' n : ℕ, negativeCoefficient f g a b (n + M + 1) := by
  have he := (summable_negativeCoefficient h).sum_add_tsum_nat_add (M + 1)
  rw [Finset.sum_range_succ', ← sum_Icc_one_eq_sum_range] at he
  simpa only [negativeCoefficient, Nat.cast_zero, mul_zero, div_zero, add_zero,
    Nat.add_assoc] using he.symm

/-- Exact truncated Poisson identity with the actual main sum and both infinite tails. -/
theorem weighted_sum_eq_poissonMain_add_remainder :
    (∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) - poissonMain f g a b M =
      poissonHeadBoundary f g b M - poissonHeadBoundary f g a M +
        (∑' n : ℕ, negativeCoefficient f g a b (n + M + 1)) -
          (∑' n, positiveCoefficient f g a b n) + poissonBoundary f g a b := by
  rw [weighted_sum_eq_fourier h, negativeCoefficient_sum_eq_head_add_tail h M,
    sum_negativeCoefficient_head h M, poissonMain_eq_zero_add_head]
  ring
end

/-- The finite endpoint expression has precisely the expected amplitude times S₁ norm. -/
theorem norm_poissonHeadBoundary {f g : ℝ → ℝ} {x : ℝ} (hg : 0 ≤ g x) (M : ℕ) :
    ‖poissonHeadBoundary f g x M‖ = g x / (2 * Real.pi) * ‖finiteS1 x M‖ := by
  rw [poissonHeadBoundary, norm_mul, norm_div, norm_weightedWave hg]
  congr 2
  simp

/-- The finite harmonic endpoint term has the printed half-integer bound even below cutoff one. -/
theorem norm_finiteS1_half_integer_le_of_pos (k : ℤ) {y : ℝ} (hy : 0 < y) :
    ‖finiteS1 ((k : ℝ) + 1 / 2) y‖ ≤ Real.log 2 + 1 / y := by
  by_cases hy1 : 1 ≤ y
  · exact norm_finiteS1_half_integer_le k hy1
  · rw [(finite_sums_eq_zero (x := (k : ℝ) + 1 / 2) (lt_of_not_ge hy1)).2, norm_zero]
    positivity

/-- The source's improved finite endpoint bound at a half-integer. -/
theorem norm_poissonHeadBoundary_half_integer_le {f g : ℝ → ℝ} {x y : ℝ}
    (hx : ∃ k : ℤ, x = (k : ℝ) + 1 / 2) (hg : 0 ≤ g x) (hy : 0 < y) :
    ‖poissonHeadBoundary f g x ⌊y⌋₊‖ ≤
      g x / (2 * Real.pi) * (Real.log 2 + 1 / y) := by
  rw [norm_poissonHeadBoundary hg]
  have he : finiteS1 x (⌊y⌋₊ : ℝ) = finiteS1 x y := by simp only [finiteS1, Nat.floor_natCast]
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  obtain ⟨k, rfl⟩ := hx
  exact norm_finiteS1_half_integer_le_of_pos k hy

end DhimanKadiriQuesadaHerrera2026
