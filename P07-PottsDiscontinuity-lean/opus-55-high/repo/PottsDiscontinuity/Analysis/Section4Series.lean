module

public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import PottsDiscontinuity.Analysis.Identity44
public import PottsDiscontinuity.Bethe.Prop21Coeff
public import PottsDiscontinuity.Bethe.RatioProducts
public import PottsDiscontinuity.Bethe.RatioProfile

/-!
# Section 4 logarithmic series and identity (4.3)

This module proves the ordered partial-sum expansion of `log (cosh λ)` and then derives
equation (4.3) using the previously proved `identity44`.  The expansion is handled as an ordered
series throughout; no absolute convergence is claimed for its limiting series.
-/

@[expose] public noncomputable section

open Complex Filter MeasureTheory Real Topology Set intervalIntegral

namespace PottsDiscontinuity

/-- The real logarithmic profile in (4.2), with its value at the single singular point
chosen as an `L¹` representative.  Every theorem identifying it with the source profile is
stated away from `α = 0`; its value there does not encode a finite value for the logarithmic
singularity. -/
def fourierP (lam α : ℝ) : ℝ :=
  if α = 0 then 0 else
    (1 / 2 : ℝ) * Real.log
      ((Real.cosh (2 * lam) - Real.cos α) / (1 - Real.cos α))

section
variable {lam c α : ℝ} (hlam : 0 < lam) (hc : c ^ 2 = 2 + 2 * Real.cosh lam) (hcos : Real.cos α < 1)
include hlam hc hcos
/-- With `c² = 2 - 2Δ = 2 + 2 cosh λ`, the Bethe factor satisfies the source modulus formula.
This is the explicit algebraic step omitted in the source's phrase “some elementary algebraic
manipulations.” -/
theorem normSq_M_kMap_eq_ratio  :
    Complex.normSq (BetheAnsatz.M c (Complex.exp (I * (Bethe.kMap lam α : ℂ)))) =
      (Real.cosh (2 * lam) - Real.cos α) / (1 - Real.cos α) := by
  have hE : 1 < Real.exp lam := by simp_all
  have hEw := Bethe.ofReal_sub_ne_zero hE (w := Complex.exp (I * α)) (by simp [Complex.norm_exp])
  have hw := Bethe.exp_I_mul_ofReal α
  have h1w : 1 - Complex.exp (I * α) ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp [hw, Complex.cos_ofReal_re] at this
    linarith
  have hE0 : (Real.exp lam : ℂ) ≠ 0 := by simp
  have hcsq : (c : ℂ) ^ 2 = ((Real.exp lam : ℂ) + 1) ^ 2 / Real.exp lam := by
    rw [← Complex.ofReal_pow, hc, Real.cosh_eq, Real.exp_neg]
    push_cast
    field_simp
    ring
  have hden : 1 - Complex.exp (I * (Bethe.kMap lam α : ℂ)) =
      ((Real.exp lam : ℂ) + 1) * (1 - Complex.exp (I * α)) / (Real.exp lam - Complex.exp (I * α)) := by
    rw [Bethe.exp_I_mul_kMap_aux hlam α, Complex.exp_neg]
    field_simp
    ring
  rw [BetheAnsatz.M, hden, hcsq, show (1 : ℂ) - ((Real.exp lam : ℂ) + 1) ^ 2 / Real.exp lam /
      (((Real.exp lam : ℂ) + 1) * (1 - Complex.exp (I * α)) / (Real.exp lam - Complex.exp (I * α))) =
      (Complex.exp (I * α) - (Real.exp lam : ℂ) ^ 2) / (Real.exp lam * (1 - Complex.exp (I * α))) by
    have : (Real.exp lam : ℂ) + 1 ≠ 0 := by exact_mod_cast (by positivity : Real.exp lam + 1 ≠ 0)
    field_simp
    ring, normSq_div, normSq_mul, hw, ← Complex.ofReal_pow]
  rw [show (Real.cos α : ℂ) + Real.sin α * I - ((Real.exp lam ^ 2 : ℝ) : ℂ) =
      ((Real.cos α - Real.exp lam ^ 2 : ℝ) : ℂ) + (Real.sin α : ℝ) * I by push_cast; ring,
    show 1 - ((Real.cos α : ℂ) + Real.sin α * I) = ((1 - Real.cos α : ℝ) : ℂ) + (-Real.sin α : ℝ) * I by
      push_cast; ring, normSq_add_mul_I, normSq_add_mul_I, normSq_ofReal,
    show Real.cosh (2 * lam) = (Real.exp lam ^ 2 + (Real.exp lam ^ 2)⁻¹) / 2 by
      rw [Real.cosh_eq, Real.exp_neg, two_mul, Real.exp_add]; ring]
  have : 1 - Real.cos α ≠ 0 := by linarith
  field_simp
  linear_combination (2 * (1 - Real.cos α) - (Real.exp lam ^ 4 + 1 - 2 * Real.cos α * Real.exp lam ^ 2)) *
    Real.sin_sq_add_cos_sq α

/-- On the punctured circle, the real profile is exactly the logarithm of the modulus of the
Bethe factor `M(e^{ik(α)})`. -/
theorem fourierP_eq_log_norm  :
    fourierP lam α = Real.log
      ‖BetheAnsatz.M c (Complex.exp (I * (Bethe.kMap lam α : ℂ)))‖ := by
  rw [fourierP, ite_eq_right (by rintro rfl; simp at hcos), ← normSq_M_kMap_eq_ratio hlam hc hcos,
    Complex.normSq_eq_norm_sq, Real.log_pow]
  ring
end

/-- The punctured derivative of the logarithmic profile, assigned an irrelevant finite value at
the singular point so that it can be used as an interval-integral representative. -/
def fourierPPrime (lam α : ℝ) : ℝ :=
  if α = 0 then 0 else
    (1 / 2 : ℝ) *
      (Real.sin α / (Real.cosh (2 * lam) - Real.cos α) -
        Real.sin α / (1 - Real.cos α))


theorem fourier_sin_product_cos_identity (n : ℕ) (α : ℝ) :
    Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) =
      (Real.cos ((n : ℝ) * α) - Real.cos (((n + 2 : ℕ) : ℝ) * α)) / 2 := by
  have h1 := Real.cos_sub (((n + 1 : ℕ) : ℝ) * α) α
  have h2 := Real.cos_add (((n + 1 : ℕ) : ℝ) * α) α
  push_cast at *
  ring_nf at *
  linarith

theorem fourierXi_cosCoeff {μ : ℝ} (hμ : 0 < μ) (n : ℕ) :
    Bethe.cosCoeff (Bethe.Xi μ) n = 2 * π * Real.exp (-μ) ^ n := by
  rw [Bethe.Xi_eq_trigSeries hμ]
  cases n with
  | zero => simp [Bethe.cosCoeff_trigSeries_zero (Bethe.summable_two_mul_exp_pow hμ) summable_zero]
  | succ n =>
    rw [Bethe.cosCoeff_trigSeries_succ (Bethe.summable_two_mul_exp_pow hμ) summable_zero]
    ring

theorem fourier_sin_kernel_integral {μ : ℝ} (hμ : 0 < μ) (n : ℕ) :
    ∫ α in (-π)..π,
      Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) /
        (Real.cosh μ - Real.cos α) =
      2 * π * Real.exp (-μ) ^ (n + 1) := by
  have h0 := fourierXi_cosCoeff hμ n
  have h2 := fourierXi_cosCoeff hμ (n + 2)
  have hc := Bethe.continuous_Xi hμ
  have hs : 0 < Real.sinh μ := by positivity
  simp only [Bethe.cosCoeff] at h0 h2
  have : ∀ α, Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) / (Real.cosh μ - Real.cos α) =
      (2 * Real.sinh μ)⁻¹ * (Bethe.Xi μ α * Real.cos (n * α) -
        Bethe.Xi μ α * Real.cos (((n + 2 : ℕ) : ℝ) * α)) := fun α => by
    rw [Bethe.Xi, fourier_sin_product_cos_identity]
    field_simp
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
    h0, h2]
  have key : 2 * Real.sinh μ * Real.exp (-μ) = 1 - Real.exp (-μ) ^ 2 := by
    rw [Real.sinh_eq, Real.exp_neg]
    field_simp
  field_simp
  linear_combination (-Real.exp (-μ) ^ n) * key

theorem fourier_ae_pos :
    ∀ᵐ α ∂volume.restrict (uIoc (-π) π), α ≠ 0 ∧ 0 < 1 - Real.cos α := by
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (Measure.ae_ne volume 0)] with α hα hα0
  rw [uIoc_of_le (by linarith [pi_pos])] at hα
  have := Bethe.ratio_one_sub_cos_lower (Ioc_subset_Icc_self hα)
  have : 0 < 2 * α ^ 2 / π ^ 2 := by positivity
  exact ⟨hα0, by linarith⟩

def fourierCotSin (n : ℕ) (α : ℝ) : ℝ :=
  if α = 0 then 0 else
    Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) / (1 - Real.cos α)

theorem fourierCotSin_integrable_integral (n : ℕ) :
    IntervalIntegrable (fun α => fourierCotSin n α) volume (-π) π ∧
      ∫ α in (-π)..π, fourierCotSin n α = 2 * π := by
  induction n with
  | zero =>
    have hEq : (fun α => fourierCotSin 0 α) =ᵐ[volume.restrict (uIoc (-π) π)]
        (fun α => 1 + Real.cos α) := by
      filter_upwards [fourier_ae_pos] with α ⟨hα0, hα⟩
      simp [fourierCotSin, hα0]
      field_simp
      nlinarith [Real.sin_sq_add_cos_sq α]
    refine ⟨(intervalIntegrable_congr_ae hEq).2 (by simp), ?_⟩
    rw [integral_congr_ae_restrict hEq]
    simp
    ring
  | succ n ih =>
    have hEq : (fun α => fourierCotSin (n + 1) α) =ᵐ[volume.restrict (uIoc (-π) π)]
        (fun α => fourierCotSin n α + Real.cos (((n + 2 : ℕ) : ℝ) * α) +
          Real.cos (((n + 1 : ℕ) : ℝ) * α)) := by
      filter_upwards [fourier_ae_pos] with α ⟨hα0, hα⟩
      have h1 := Real.sin_add (((n + 1 : ℕ) : ℝ) * α) α
      have h2 := Real.cos_add (((n + 1 : ℕ) : ℝ) * α) α
      simp only [fourierCotSin, hα0, ite_false]
      push_cast at *
      field_simp
      ring_nf at *
      rw [h1, h2]
      linear_combination Real.cos (↑n * α + α) * Real.sin_sq_add_cos_sq α
    have hc : ∀ m : ℕ, IntervalIntegrable (fun α => Real.cos ((m : ℝ) * α)) volume (-π) π :=
      fun m => Continuous.intervalIntegrable (by fun_prop) _ _
    refine ⟨((ih.1.add (hc _)).add (hc _)).congr_ae hEq.symm, ?_⟩
    rw [integral_congr_ae_restrict hEq, integral_add (ih.1.add (hc _)) (hc _),
      integral_add ih.1 (hc _), ih.2, Bethe.integral_cos_nat_mul (by omega),
      Bethe.integral_cos_nat_mul (by omega)]
    ring

theorem fourierP_prime_sine_integral {lam : ℝ} (hlam : 0 < lam)
    (m : ℕ) (hm : 0 < m) :
    (1 / π) * ∫ α in (-π)..π,
      fourierPPrime lam α * Real.sin ((m : ℝ) * α) =
      Real.exp (-2 * lam * (m : ℝ)) - 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hcot := fourierCotSin_integrable_integral n
  have hcosh : 1 < Real.cosh (2 * lam) := by aesop
  rw [integral_congr_ae_restrict (g := fun α => (1 / 2 : ℝ) *
      (Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) / (Real.cosh (2 * lam) - Real.cos α) -
        fourierCotSin n α)) (by filter_upwards [fourier_ae_pos] with α ⟨hα0, _⟩; grind [fourierPPrime, fourierCotSin]),
    intervalIntegral.integral_const_mul, integral_sub (Continuous.intervalIntegrable
      (by fun_prop (disch := intro α; linarith [Real.cos_le_one α])) _ _) hcot.1, hcot.2,
    fourier_sin_kernel_integral (by positivity), ← Real.exp_nat_mul]
  field_simp

theorem fourierP_hasDerivAt {lam α : ℝ} (hlam : 0 < lam)
    (hα : α ∈ Ioo (-π) π) (hα0 : α ≠ 0) :
    HasDerivAt (fourierP lam) (fourierPPrime lam α) α := by
  have := Bethe.ratio_one_sub_cos_lower (Ioo_subset_Icc_self hα)
  have h2 : 0 < 2 * α ^ 2 / π ^ 2 := by positivity
  have hcosh : 1 < Real.cosh (2 * lam) := by aesop
  have h3 : 1 - Real.cos α ≠ 0 := by linarith
  have h4 : Real.cosh (2 * lam) - Real.cos α ≠ 0 := by linarith [Real.cos_le_one α]
  have hd := ((((Real.hasDerivAt_cos α).const_sub (Real.cosh (2 * lam))).div
    ((Real.hasDerivAt_cos α).const_sub 1) h3).log (div_ne_zero h4 h3)).const_mul (1 / 2 : ℝ)
  refine (hd.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp [fourierPPrime, hα0]
    field_simp
  · filter_upwards [eventually_ne_nhds hα0] with x hx
    simp [fourierP, hx]


/-- The ordered partial sums in the paper's logarithmic expansion converge to
`λ - log (cosh λ)`, so `log (cosh λ) = λ - ∑_{m>0} (-1)^m (e^{-2λm}-1)/m`. -/
theorem tendsto_logCoshExpPartial {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc 1 N, (-1 : ℝ) ^ m / m * (Real.exp (-2 * lam * m) - 1))
      atTop (𝓝 (lam - Real.log (Real.cosh lam))) := by
  set q := Real.exp (-2 * lam)
  have hq : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by simp [q, hlam]
  have hx : ∀ x ∈ uIcc q 1, 1 + x ≠ 0 := fun x hx => by
    rw [uIcc_of_le hq1.le] at hx
    linarith [hx.1]
  have hI : ∀ N : ℕ, IntervalIntegrable (fun x : ℝ => (-x) ^ N / (1 + x)) volume q 1 := fun N =>
    ContinuousOn.intervalIntegrable (by fun_prop)
  have key : ∀ N : ℕ, ∑ m ∈ Finset.Icc 1 N, (-1 : ℝ) ^ m / m * (Real.exp (-2 * lam * m) - 1) =
      lam - Real.log (Real.cosh lam) - ∫ x in q..1, (-x) ^ N / (1 + x) := by
    intro N
    induction N with
    | zero =>
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      simp only [pow_zero]
      rw [intervalIntegral.integral_comp_add_left (fun x => 1 / x), integral_one_div_of_pos (by linarith)
        (by norm_num), show (1 + 1) / (1 + q) = Real.exp lam / Real.cosh lam by
          rw [Real.cosh_eq, show Real.exp (-lam) = Real.exp lam * q by rw [← Real.exp_add]; ring_nf]
          field_simp
          ring, Real.log_div (by positivity) (by positivity), Real.log_exp]
      ring
    | succ N ih =>
      have h := integral_sub (hI (N + 1)) (hI N)
      rw [integral_congr (g := fun x => -(-x) ^ N) fun y hy => by
          have := hx y hy
          field_simp
          ring, intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg (fun x => x ^ N),
        integral_pow] at h
      rw [Finset.sum_Icc_succ_top (by omega), ih, show -2 * lam * ((N + 1 : ℕ) : ℝ) =
        ((N + 1 : ℕ) : ℝ) * (-2 * lam) by ring, Real.exp_nat_mul]
      push_cast
      linear_combination -h
  have h0 : Tendsto (fun N : ℕ => ∫ x in q..1, (-x) ^ N / (1 + x)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun N => (intervalIntegral.norm_integral_le_of_norm_le hq1.le
      (ae_of_all _ fun x hx => ?_) ((continuous_pow N).intervalIntegrable _ _)).trans
        ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  · simpa using (tendsto_const_nhds.sub h0).congr fun N => (key N).symm
  · rw [norm_div, norm_pow, norm_neg, Real.norm_of_nonneg (by linarith [hx.1]),
      Real.norm_of_nonneg (by linarith [hx.1])]
    exact div_le_self (pow_nonneg (by linarith [hx.1]) _) (by linarith [hx.1])
  · simp [integral_pow]
    rw [← one_div]
    gcongr
    exact sub_le_self _ (by positivity)

/-! ### The algebra of (4.3) and its ordered partial sums -/

section
variable (lam : ℝ) (N : ℕ)
/-- The ordered partial sums of `∑ (-1)^m tanh(λm)/m`. -/
def altTanhPartial  : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, (-1 : ℝ) ^ m / (m : ℝ) * Real.tanh ((m : ℝ) * lam)

/-- The ordered partial sums of the correction term in (4.3). -/
def logCoshTauCorrectionPartial  : ℝ :=
  ∑ m ∈ Finset.Icc 1 N,
    (-1 : ℝ) ^ m / (m : ℝ) * Real.tanh ((m : ℝ) * lam) *
      (Real.exp (-2 * lam * m) - 1)
end

theorem tanh_exp_identity (x : ℝ) :
    (1 + Real.tanh x) * (Real.exp (-2 * x) - 1) = -2 * Real.tanh x := by
  rw [Real.tanh_eq, show -2 * x = -x - x by ring, Real.exp_sub]
  field_simp
  ring

/-- **Equation (4.3)** in ordered-partial-sum form. The left series converges as a consequence
of the identity with the convergent expansion of `log(cosh λ)` and the convergence in `identity44`.
The right-hand convergence and the value relation are included. -/
theorem identity43 (lam : ℝ) (hlam : 0 < lam) :
    ∃ S : ℝ,
      Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      Tendsto (fun N => Real.log (Real.cosh lam) - logCoshTauCorrectionPartial lam N)
        atTop (𝓝 (lam + 2 * S)) := by
  obtain ⟨S, _, hS, -⟩ := identity44 lam hlam
  refine ⟨S, hS, ?_⟩
  convert (tendsto_const_nhds (x := Real.log (Real.cosh lam))).add
    ((tendsto_logCoshExpPartial hlam).add (hS.const_mul 2)) using 1
  · funext N
    simp only [logCoshTauCorrectionPartial, Finset.mul_sum, ← Finset.sum_add_distrib,
      sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    have := tanh_exp_identity (m * lam)
    rw [show -2 * (m * lam) = -2 * lam * m by ring] at this
    linear_combination (-(-1 : ℝ) ^ m / m) * this
  · ring

end PottsDiscontinuity
