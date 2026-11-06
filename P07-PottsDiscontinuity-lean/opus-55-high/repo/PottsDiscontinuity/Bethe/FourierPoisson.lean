module

public import Mathlib
public import PottsDiscontinuity.Bethe.KMap

/-!
# Fourier analysis of the Poisson kernel `Ξ_μ` on `[-π, π]`

Source: arXiv:1611.09877v2, §2.1 (proof of Proposition 2.1) and §4 (Fourier computations).
This file replaces the residue computation `Ξ̂_μ(m) = e^{-μ|m|}` of §4 by the elementary geometric
series for the Poisson kernel

  `Ξ_μ(α) = sinh μ / (cosh μ - cos α) = 1 + 2 ∑_{m ≥ 1} e^{-μ m} cos (m α)`   (`hasSum_Xi_cos`),

which is absolutely and uniformly convergent for `μ > 0`.  Everything is phrased with real cosine
and sine coefficients.  The main results are:

* `hasSum_xiConv`: for `g` integrable on `[-π, π]`, the convolution operator
  `xiConv μ g α = (1/2π) ∫_{-π}^{π} Ξ_μ(α - β) g(β) dβ` has the absolutely convergent expansion
  `(1/2π) ∫ g + (1/π) ∑_{m≥1} e^{-μ m} (cos(mα) ∫ g cos(m·) + sin(mα) ∫ g sin(m·))`
  (this is the Fourier-coefficient statement `\widehat{Ξ_μ * g}(m) = e^{-μ|m|} ĝ(m)`);
* `integral_mul_xiConv_nonneg`: `∫_{-π}^{π} g · (Ξ_μ * g) ≥ 0` (positive definiteness of `Ξ_μ`);
* `eq_zero_of_eq_neg_xiConv`: an integrable `D` with `D = -(Ξ_μ * D)` on `[-π, π]` vanishes a.e.
  (this is the uniqueness half of Proposition 2.1: `(1 + e^{-μ|m|}) D̂(m) = 0` for all `m`).
-/

@[expose] public noncomputable section

open Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe


/-- Poisson kernel series: `Ξ_μ(α) = 1 + 2 ∑_{m ≥ 1} e^{-μ m} cos(m α)` for `μ > 0`. -/
theorem hasSum_Xi_cos {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    HasSum (fun n : ℕ => 2 * Real.exp (-μ) ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * α))
      (Xi μ α - 1) := by
  set r := Real.exp (-μ)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by simp [r, hμ]
  set z : ℂ := r * Complex.exp (α * Complex.I)
  have hz : ‖z‖ < 1 := by simp [z, Complex.norm_exp_ofReal_mul_I, abs_of_pos hr, hr1]
  convert (Complex.hasSum_re ((hasSum_geometric_of_norm_lt_one hz).mul_left z)).mul_left 2 using 1
  · funext n
    rw [← pow_succ', mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow,
      show ((n + 1 : ℕ) : ℂ) * (α * Complex.I) = (((n + 1 : ℕ) : ℝ) * α : ℝ) * Complex.I by push_cast; ring,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, mul_assoc]
  · have hc := Real.cos_le_one α
    have he : rexp μ = r⁻¹ := by simp [r, Real.exp_neg]
    rw [← div_eq_mul_inv, Complex.div_re]
    simp [z, Xi, Complex.normSq_apply, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Real.sinh_eq, Real.cosh_eq, he, show rexp (-μ) = r from rfl]
    have : 1 + r ^ 2 - r * 2 * cos α ≠ 0 := by nlinarith
    rw [show (1 - r * cos α) * (1 - r * cos α) + r * sin α * (r * sin α) = 1 + r ^ 2 - r * 2 * cos α by
      linear_combination r ^ 2 * sin_sq_add_cos_sq α]
    field_simp
    linear_combination 2 * r ^ 2 * sin_sq_add_cos_sq α

theorem continuous_Xi {μ : ℝ} (hμ : 0 < μ) : Continuous (Xi μ) :=
  continuous_const.div (continuous_const.sub continuous_cos) fun α => by
    linarith [cos_le_one α, one_lt_cosh.2 hμ.ne']

/-! ### Orthogonality on `[-π, π]` -/

theorem integral_cos_int (k : ℤ) :
    ∫ x in (-π)..π, cos (k * x) = if k = 0 then 2 * π else 0 := by
  split_ifs <;> simp_all; ring

theorem integral_sin_int (k : ℤ) : ∫ x in (-π)..π, sin (k * x) = 0 := by
  by_cases k = 0 <;> simp_all

theorem intervalIntegrable_cos_mul (k : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.cos (k * x)) volume (-π) π :=
  (by fun_prop : Continuous _).intervalIntegrable _ _

theorem intervalIntegrable_sin_mul (k : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.sin (k * x)) volume (-π) π :=
  (by fun_prop : Continuous _).intervalIntegrable _ _

section
variable {m n : ℕ} (hn : n ≠ 0)
include hn
/-- Orthogonality: `∫_{-π}^{π} cos(m x) cos(n x) dx = π δ_{mn}` for `m, n ≥ 1`. -/
theorem integral_cos_mul_cos_pos  :
    ∫ x in (-π)..π, Real.cos (m * x) * Real.cos (n * x) = if m = n then π else 0 := by
  simp_rw [fun x => show cos (m * x) * cos (n * x) =
    (cos (((m : ℤ) - n : ℤ) * x) + cos (((m : ℤ) + n : ℤ) * x)) / 2 by
      push_cast; rw [sub_mul, add_mul, cos_sub, cos_add]; ring]
  rw [intervalIntegral.integral_div, integral_add (intervalIntegrable_cos_mul _) (intervalIntegrable_cos_mul _),
    integral_cos_int, integral_cos_int]
  split_ifs <;> first | omega | ring

theorem integral_sin_mul_sin_pos  :
    ∫ x in (-π)..π, Real.sin (m * x) * Real.sin (n * x) = if m = n then π else 0 := by
  simp_rw [fun x => show sin (m * x) * sin (n * x) =
    (cos (((m : ℤ) - n : ℤ) * x) - cos (((m : ℤ) + n : ℤ) * x)) / 2 by
      push_cast; rw [sub_mul, add_mul, cos_sub, cos_add]; ring]
  rw [intervalIntegral.integral_div, integral_sub (intervalIntegrable_cos_mul _) (intervalIntegrable_cos_mul _),
    integral_cos_int, integral_cos_int]
  split_ifs <;> first | omega | ring
end

theorem integral_sin_mul_cos_nat (m n : ℕ) :
    ∫ x in (-π)..π, Real.sin (m * x) * Real.cos (n * x) = 0 := by
  simp_rw [fun x => show sin (m * x) * cos (n * x) =
    (sin (((m : ℤ) - n : ℤ) * x) + sin (((m : ℤ) + n : ℤ) * x)) / 2 by
      push_cast; rw [sub_mul, add_mul, sin_sub, sin_add]; ring]
  rw [intervalIntegral.integral_div, integral_add (intervalIntegrable_sin_mul _) (intervalIntegrable_sin_mul _),
    integral_sin_int, integral_sin_int]
  simp

theorem integral_cos_nat_mul {m : ℕ} (hm : m ≠ 0) : ∫ x in (-π)..π, Real.cos (m * x) = 0 := by
  simp_all

theorem integral_sin_nat_mul (m : ℕ) : ∫ x in (-π)..π, Real.sin (m * x) = 0 := by
  simpa using integral_sin_int m

/-- `xiConv μ g α = (1/2π) ∫_{-π}^{π} Ξ_μ(α - β) g(β) dβ`. -/
def xiConv (μ : ℝ) (g : ℝ → ℝ) (α : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ β in (-π)..π, Xi μ (α - β) * g β

section
variable (g : ℝ → ℝ) (m : ℕ)
/-- Cosine coefficient `∫_{-π}^{π} g(β) cos(m β) dβ` (unnormalised). -/
def cosCoeff  : ℝ := ∫ β in (-π)..π, g β * Real.cos (m * β)

/-- Sine coefficient `∫_{-π}^{π} g(β) sin(m β) dβ` (unnormalised). -/
def sinCoeff  : ℝ := ∫ β in (-π)..π, g β * Real.sin (m * β)
end

theorem cosCoeff_zero (g : ℝ → ℝ) : cosCoeff g 0 = ∫ β in (-π)..π, g β := by
  simp [cosCoeff]

/-- Termwise integration of `∑ φ_n g` over `[-π, π]` for continuous `φ_n` with summable uniform
bounds and integrable `g`. -/
theorem hasSum_integral_mul {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-π) π)
    {φ : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {C : ℕ → ℝ} (hC : Summable C)
    (hφ : ∀ n, Continuous (φ n)) (hb : ∀ n β, |φ n β| ≤ C n)
    (hs : ∀ β, HasSum (fun n => φ n β * g β) (f β)) :
    HasSum (fun n => ∫ β in (-π)..π, φ n β * g β) (∫ β in (-π)..π, f β) :=
  hasSum_integral_of_dominated_convergence (fun n β => C n * ‖g β‖)
    (fun n => (hφ n).aestronglyMeasurable.mul hg.def'.aestronglyMeasurable)
    (fun n => .of_forall fun β _ => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hb n β) (norm_nonneg _))
    (.of_forall fun β _ => hC.mul_right _)
    (by simp_rw [tsum_mul_right]; exact hg.norm.const_mul _) (.of_forall fun β _ => hs β)

theorem summable_exp_pow {μ : ℝ} (hμ : 0 < μ) (K : ℝ) :
    Summable fun n : ℕ => K * exp (-μ) ^ (n + 1) :=
  ((summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (exp_pos _).le (by simp [hμ]))).mul_left K

theorem integral_trig_mul {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-π) π)
    (C a b : ℝ) (m : ℕ) : ∫ β in (-π)..π, C * (cos (m * β) * a + sin (m * β) * b) * g β =
      C * (a * cosCoeff g m + b * sinCoeff g m) := by
  rw [cosCoeff, sinCoeff, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← integral_add ((hg.mul_continuousOn (by fun_prop)).const_mul _)
    ((hg.mul_continuousOn (by fun_prop)).const_mul _), ← intervalIntegral.integral_const_mul]
  congr 1
  funext β
  ring

theorem hasSum_xiConv {μ : ℝ} (hμ : 0 < μ) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (-π) π) (α : ℝ) :
    HasSum (fun n : ℕ => π⁻¹ * Real.exp (-μ) ^ (n + 1) *
        (Real.cos (((n + 1 : ℕ) : ℝ) * α) * cosCoeff g (n + 1) +
          Real.sin (((n + 1 : ℕ) : ℝ) * α) * sinCoeff g (n + 1)))
      (xiConv μ g α - (2 * π)⁻¹ * cosCoeff g 0) := by
  have h := hasSum_integral_mul hg (summable_exp_pow hμ π⁻¹)
    (φ := fun n β => π⁻¹ * exp (-μ) ^ (n + 1) * cos (((n + 1 : ℕ) : ℝ) * (α - β)))
    (f := fun β => (2 * π)⁻¹ * ((Xi μ (α - β) - 1) * g β)) (fun n => by fun_prop)
    (fun n β => by
      rw [abs_mul, abs_of_pos (by positivity)]
      exact mul_le_of_le_one_right (by positivity) (abs_cos_le_one _))
    (fun β => by
      convert ((hasSum_Xi_cos hμ (α - β)).mul_right (g β)).mul_left (2 * π)⁻¹ using 2
      field_simp)
  convert h using 1
  · funext n
    rw [← integral_trig_mul hg]
    congr 1
    funext β
    rw [mul_sub, cos_sub]
    ring
  · rw [intervalIntegral.integral_const_mul, xiConv, cosCoeff_zero, ← mul_sub, ← integral_sub _ hg]
    · simp_rw [sub_mul, one_mul]
    exact hg.continuousOn_mul ((continuous_Xi hμ).comp (by fun_prop)).continuousOn

theorem continuous_xiConv {μ : ℝ} (hμ : 0 < μ) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (-π) π) : Continuous (xiConv μ g) :=
  continuous_const.mul (continuous_of_dominated_interval
    (fun α => (((continuous_Xi hμ).comp (by fun_prop)).aestronglyMeasurable).mul
      hg.def'.aestronglyMeasurable)
    (fun α => .of_forall fun β _ => by
      rw [norm_mul, norm_of_nonneg (Xi_pos hμ _).le]
      exact mul_le_mul_of_nonneg_right (Xi_bounds hμ _).2 (norm_nonneg _))
    (hg.norm.const_mul _) (.of_forall fun β _ => ((continuous_Xi hμ).comp (by fun_prop)).mul continuous_const))

/-- Positive definiteness of the Poisson kernel: `∫ g · (Ξ_μ * g) ≥ 0`. -/
theorem integral_mul_xiConv_nonneg {μ : ℝ} (hμ : 0 < μ) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (-π) π) :
    0 ≤ ∫ α in (-π)..π, g α * xiConv μ g α := by
  have hpi := pi_pos
  have h := hasSum_integral_mul hg (summable_exp_pow hμ (π⁻¹ * (2 * ∫ β in (-π)..π, |g β|))) (fun n => by fun_prop)
    (fun n β => by
      have hc : ∀ m, |cosCoeff g m| ≤ ∫ β in (-π)..π, |g β| ∧ |sinCoeff g m| ≤ ∫ β in (-π)..π, |g β| := fun m => by
        rw [cosCoeff, sinCoeff, ← norm_eq_abs, ← norm_eq_abs]
        constructor <;> refine norm_integral_le_of_norm_le (by linarith) (.of_forall fun β _ => ?_) hg.abs <;>
          simpa using mul_le_of_le_one_right (abs_nonneg _) (by first | exact abs_cos_le_one _ | exact abs_sin_le_one _)
      obtain ⟨h1, h2⟩ := hc (n + 1)
      have := abs_add_le (cos (((n + 1 : ℕ) : ℝ) * β) * cosCoeff g (n + 1)) (sin (((n + 1 : ℕ) : ℝ) * β) * sinCoeff g (n + 1))
      rw [abs_mul, abs_mul] at this
      rw [abs_mul, abs_of_pos (by positivity)]
      refine (mul_le_mul_of_nonneg_left (this.trans (?_ : _ ≤ 2 * ∫ β in (-π)..π, |g β|))
        (by positivity)).trans_eq (by ring)
      nlinarith [abs_cos_le_one (((n + 1 : ℕ) : ℝ) * β), abs_sin_le_one (((n + 1 : ℕ) : ℝ) * β),
        abs_nonneg (cosCoeff g (n + 1)), abs_nonneg (sinCoeff g (n + 1))])
    (fun β => (hasSum_xiConv hμ hg β).mul_right (g β))
  simp_rw [integral_trig_mul hg] at h
  have := h.nonneg fun n => mul_nonneg (by positivity) (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
  rw [show (fun α => g α * xiConv μ g α) = fun α => (xiConv μ g α - (2 * π)⁻¹ * cosCoeff g 0) * g α
    + (2 * π)⁻¹ * cosCoeff g 0 * g α by funext; ring, intervalIntegral.integral_add _ (hg.const_mul _),
    intervalIntegral.integral_const_mul]
  exact add_nonneg this (by rw [mul_assoc, ← cosCoeff_zero]; exact mul_nonneg (by positivity) (mul_self_nonneg _))
  exact hg.continuousOn_mul ((continuous_xiConv hμ hg).sub continuous_const).continuousOn

theorem eq_zero_of_eq_neg_xiConv {μ : ℝ} (hμ : 0 < μ) {D : ℝ → ℝ} (hD : IntervalIntegrable D volume (-π) π)
    (h : ∀ α ∈ Ioc (-π) π, D α = -xiConv μ D α) :
    D =ᵐ[volume.restrict (Ioc (-π) π)] 0 := by
  have hpi := pi_pos
  have hnn := integral_mul_xiConv_nonneg hμ hD
  have e : ∀ᵐ α ∂volume.restrict (Ioc (-π) π), -(D α * xiConv μ D α) = D α ^ 2 :=
    (ae_restrict_mem measurableSet_Ioc).mono fun α hα => by rw [h α hα]; ring
  rw [integral_of_le (by linarith), ← neg_nonpos, ← MeasureTheory.integral_neg, integral_congr_ae e] at hnn
  filter_upwards [(integral_eq_zero_iff_of_nonneg (fun α => sq_nonneg (D α))
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1
      (hD.mul_continuousOn (continuous_xiConv hμ hD).continuousOn)).neg.congr e)).1
    (hnn.antisymm (integral_nonneg fun α => sq_nonneg _))] with α hα
  simpa using hα

end PottsDiscontinuity.Bethe
