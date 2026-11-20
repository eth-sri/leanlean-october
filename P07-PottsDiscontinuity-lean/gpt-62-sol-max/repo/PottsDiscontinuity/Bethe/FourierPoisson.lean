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
* The positive normalized kernel cannot have a nonzero eigenfunction with eigenvalue `-1`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

/-! ### The Poisson kernel series -/

noncomputable def diskDen (r α : ℝ) : ℝ := 1 - 2 * r * Real.cos α + r ^ 2

noncomputable def sineKernel (r α : ℝ) : ℝ := r * Real.sin α / diskDen r α

theorem diskDen_eq (r α : ℝ) : diskDen r α = (1 - r)^2 + 2*r*(1 - Real.cos α) := by
  unfold diskDen
  ring

theorem diskDen_pos {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (α : ℝ) : 0 < diskDen r α := by
  rw [diskDen_eq]
  have : 0 < 1 - r := sub_pos.mpr hr1
  have : 0 ≤ 1 - Real.cos α := sub_nonneg.mpr (Real.cos_le_one α)
  positivity

private theorem geom_circle {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (α : ℝ) :
    HasSum (fun n : ℕ => r ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * α))
      ((r * Real.cos α - r^2) / diskDen r α) ∧
    HasSum (fun n : ℕ => r ^ (n + 1) * Real.sin (((n + 1 : ℕ) : ℝ) * α)) (sineKernel r α) := by
  let z : ℂ := (r : ℂ) * Complex.exp (α * Complex.I)
  have hz : ‖z‖ < 1 := by
    simpa [z, abs_of_pos hr] using hr1
  have h := (hasSum_geometric_of_norm_lt_one hz).mul_left z
  have hd : 1 - z ≠ 0 := sub_ne_zero.mpr fun he => by simp [← he] at hz
  have hv : z * (1 - z)⁻¹ = (1 - z)⁻¹ - 1 := by field_simp; ring
  rw [hv] at h
  have ha (n : ℕ) : z * z ^ n =
      (r ^ (n + 1) : ℝ) * Complex.exp ((((n + 1 : ℕ) : ℝ) * α : ℝ) * Complex.I) := by
    rw [← pow_succ', show z = _ from rfl, mul_pow, ← Complex.ofReal_pow, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hre : z.re = r * Real.cos α := by simp [z]
  have him : z.im = r * Real.sin α := by simp [z]
  have hns : Complex.normSq (1 - z) = diskDen r α := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hre, him]
    simp only [Complex.one_re, Complex.one_im, zero_sub, diskDen]
    linear_combination (r^2) * Real.sin_sq_add_cos_sq α
  have H := (Complex.hasSum_iff _ _).mp h
  simp only [ha, Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.sub_re, Complex.sub_im, Complex.inv_re, Complex.inv_im,
    Complex.one_re, Complex.one_im, hre, him, hns, zero_sub, neg_neg, sub_zero] at H
  refine ⟨?_, H.2⟩
  convert H.1 using 1
  have hp := (diskDen_pos hr.le hr1 α).ne'
  field_simp
  unfold diskDen
  ring

theorem hasSum_sineKernel {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (α : ℝ) :
    HasSum (fun n : ℕ => r ^ (n + 1) * Real.sin (((n + 1 : ℕ) : ℝ) * α)) (sineKernel r α) :=
  (geom_circle hr hr1 α).2

private theorem cosh_exp_neg (μ : ℝ) :
    Real.cosh μ = ((Real.exp (-μ))⁻¹ + Real.exp (-μ)) / 2 := by
  simp [Real.cosh_eq, Real.exp_neg]

theorem sineKernel_exp_neg (μ α : ℝ) :
    sineKernel (Real.exp (-μ)) α = (1 / 2) * (Real.sin α / (Real.cosh μ - Real.cos α)) := by
  rw [sineKernel, cosh_exp_neg]
  have he := (Real.exp_pos (-μ)).ne'
  set r := Real.exp (-μ)
  rw [show (r⁻¹ + r) / 2 - Real.cos α = diskDen r α / (2*r) by unfold diskDen; field_simp; ring]
  rw [div_div_eq_mul_div]
  ring

/-- Poisson kernel series on the circle. -/
theorem hasSum_Xi_cos {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    HasSum (fun n : ℕ => 2 * Real.exp (-μ) ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * α))
      (Xi μ α - 1) := by
  have hr := Real.exp_pos (-μ)
  have hr1 : Real.exp (-μ) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hμ)
  have h := (geom_circle hr hr1 α).1.mul_left 2
  convert h using 1
  · funext n; ring
  unfold Xi
  rw [cosh_exp_neg, show Real.sinh μ = ((Real.exp (-μ))⁻¹ - Real.exp (-μ)) / 2 by
    simp [Real.sinh_eq, Real.exp_neg]]
  set r := Real.exp (-μ)
  have hd := (diskDen_pos hr.le hr1 α).ne'
  rw [show (r⁻¹ + r) / 2 - Real.cos α = diskDen r α / (2*r) by unfold diskDen; field_simp; ring]
  field_simp
  unfold diskDen
  ring

theorem continuous_Xi {μ : ℝ} (hμ : 0 < μ) : Continuous (Xi μ) := by
  unfold Xi
  refine continuous_const.div (continuous_const.sub Real.continuous_cos) fun α => ?_
  have h2 := Real.one_lt_cosh.mpr hμ.ne'
  have := Real.cos_le_one α
  linarith

/-! ### Orthogonality on `[-π, π]` -/

theorem integral_cos_int_mul {k : ℤ} (hk : k ≠ 0) : ∫ x in (-π)..π, Real.cos (k * x) = 0 := by
  simp_all

theorem integral_odd_eq_zero {f : ℝ → ℝ} (hf : ∀ x, f (-x) = -f x) :
    ∫ x in (-π)..π, f x = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -π) (b := π) f
  simp only [neg_neg] at h
  simp_rw [hf] at h
  rw [intervalIntegral.integral_neg] at h
  linarith

section

variable (m n : ℕ) (x : ℝ)

theorem cos_mul_cos_nat : Real.cos (m * x) * Real.cos (n * x) =
      (Real.cos (((m : ℤ) - n : ℤ) * x) + Real.cos (((m : ℤ) + n : ℤ) * x)) / 2 := by
  push_cast
  have := two_mul_cos_mul_cos (m * x) (n * x)
  grind

theorem sin_mul_sin_nat : Real.sin (m * x) * Real.sin (n * x) =
      (Real.cos (((m : ℤ) - n : ℤ) * x) - Real.cos (((m : ℤ) + n : ℤ) * x)) / 2 := by
  push_cast
  rw [show ((m:ℝ) - n) * x = m * x - n * x by ring, show ((m:ℝ) + n) * x = m * x + n * x by ring,
    Real.cos_sub, Real.cos_add]
  ring

end

theorem intervalIntegrable_cos_mul (k : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.cos (k * x)) volume (-π) π :=
  (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _

private theorem integral_mode_diff {m n : ℕ} (hn : n ≠ 0) (a : ℝ) :
    (∫ x in (-π)..π, (Real.cos ((((m : ℤ) - n : ℤ) : ℝ) * x) +
      a * Real.cos ((((m : ℤ) + n : ℤ) : ℝ) * x)) / 2) = if m = n then π else 0 := by
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (intervalIntegrable_cos_mul _) ((intervalIntegrable_cos_mul _).const_mul _),
    intervalIntegral.integral_const_mul, integral_cos_int_mul (by omega : (m : ℤ) + n ≠ 0), mul_zero, add_zero]
  by_cases h : m = n
  · subst n
    simp
  · rw [integral_cos_int_mul (by omega : (m : ℤ) - n ≠ 0)]
    simp [h]

/-- Orthogonality: `∫_{-π}^{π} cos(m x) cos(n x) dx = π δ_{mn}` for `m, n ≥ 1`. -/
theorem integral_cos_mul_cos_pos {m n : ℕ} (_hm : m ≠ 0) (hn : n ≠ 0) :
    ∫ x in (-π)..π, Real.cos (m * x) * Real.cos (n * x) = if m = n then π else 0 := by
  simpa [cos_mul_cos_nat] using integral_mode_diff (m := m) hn 1

theorem integral_sin_mul_sin_pos {m n : ℕ} (_hm : m ≠ 0) (hn : n ≠ 0) :
    ∫ x in (-π)..π, Real.sin (m * x) * Real.sin (n * x) = if m = n then π else 0 := by
  simpa [← sub_eq_add_neg, sin_mul_sin_nat] using integral_mode_diff (m := m) hn (-1)

theorem integral_sin_mul_cos_nat (m n : ℕ) :
    ∫ x in (-π)..π, Real.sin (m * x) * Real.cos (n * x) = 0 := by
  exact integral_odd_eq_zero (fun x => by simp)

theorem integral_cos_nat_mul {m : ℕ} (hm : m ≠ 0) : ∫ x in (-π)..π, Real.cos (m * x) = 0 := by
  simp_all

theorem integral_sin_nat_mul (m : ℕ) : ∫ x in (-π)..π, Real.sin (m * x) = 0 := by
  exact integral_odd_eq_zero (fun x => by simp)

/-! ### The convolution operator `g ↦ Ξ_μ * g / 2π` and its coefficient expansion -/

/-- `xiConv μ g α = (1/2π) ∫_{-π}^{π} Ξ_μ(α - β) g(β) dβ`. -/
noncomputable def xiConv (μ : ℝ) (g : ℝ → ℝ) (α : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ β in (-π)..π, Xi μ (α - β) * g β

/-- Cosine coefficient `∫_{-π}^{π} g(β) cos(m β) dβ` (unnormalised). -/
noncomputable def cosCoeff (g : ℝ → ℝ) (m : ℕ) : ℝ := ∫ β in (-π)..π, g β * Real.cos (m * β)

/-- Sine coefficient `∫_{-π}^{π} g(β) sin(m β) dβ` (unnormalised). -/
noncomputable def sinCoeff (g : ℝ → ℝ) (m : ℕ) : ℝ := ∫ β in (-π)..π, g β * Real.sin (m * β)

section

variable (a b : ℕ → ℝ) (n : ℕ)

/-- The general term of a trigonometric series. -/
noncomputable def trigTerm (α : ℝ) : ℝ :=
  a n * Real.cos (((n + 1 : ℕ) : ℝ) * α) + b n * Real.sin (((n + 1 : ℕ) : ℝ) * α)

theorem abs_trigTerm_le (α : ℝ) : |trigTerm a b n α| ≤ |a n| + |b n| := by
  unfold trigTerm
  refine (abs_add_le ..).trans (add_le_add ?_ ?_)
  · simpa using mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

theorem continuous_trigTerm : Continuous (trigTerm a b n) := by
  unfold trigTerm; fun_prop

end

theorem hasSum_trigTerm {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (α : ℝ) :
    HasSum (fun n => trigTerm a b n α) (∑' n, trigTerm a b n α) := by
  refine Summable.hasSum ?_
  refine Summable.of_norm_bounded (g := fun n => |a n| + |b n|) (ha.abs.add hb.abs) ?_
  intro n
  rw [Real.norm_eq_abs]
  exact abs_trigTerm_le a b n α

theorem integral_trigTerm_mul (a b : ℕ → ℝ) (n : ℕ) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (-π) π) :
    ∫ β in (-π)..π, trigTerm a b n β * g β =
      a n * cosCoeff g (n + 1) + b n * sinCoeff g (n + 1) := by
  unfold cosCoeff sinCoeff
  simp only [trigTerm, add_mul, mul_assoc, mul_comm (Real.cos _), mul_comm (Real.sin _)]
  rw [intervalIntegral.integral_add
    ((hg.mul_continuousOn (by fun_prop)).const_mul _)
    ((hg.mul_continuousOn (by fun_prop)).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- Integrate an absolutely convergent trigonometric series against an integrable function. -/
theorem hasSum_integral_trigTerm_mul {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b)
    {g f : ℝ → ℝ} (hg : IntervalIntegrable g volume (-π) π)
    (hf : ∀ β, HasSum (fun n => trigTerm a b n β) (f β)) :
    HasSum (fun n => ∫ β in (-π)..π, trigTerm a b n β * g β) (∫ β in (-π)..π, f β * g β) := by
  let c := fun n => |a n| + |b n|
  have hc : Summable c := ha.abs.add hb.abs
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (fun n β => c n * ‖g β‖) (fun n => (continuous_trigTerm a b n).aestronglyMeasurable.mul
      (intervalIntegrable_iff.mp hg).aestronglyMeasurable) ?_ ?_ ?_ ?_
  · exact fun n => .of_forall fun β _ => by
      rw [norm_mul, Real.norm_eq_abs (trigTerm a b n β)]
      exact mul_le_mul_of_nonneg_right (abs_trigTerm_le a b n β) (norm_nonneg _)
  · exact .of_forall fun β _ => hc.mul_right _
  · simpa [tsum_mul_right] using hg.norm.const_mul (∑' n, c n)
  · exact .of_forall fun β _ => (hf β).mul_right _

theorem intervalIntegrable_Xi_mul {μ : ℝ} (hμ : 0 < μ) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume (-π) π) (α : ℝ) :
    IntervalIntegrable (fun β => Xi μ (α - β) * f β) volume (-π) π :=
  hf.continuousOn_mul ((continuous_Xi hμ).comp (by fun_prop)).continuousOn

theorem hasSum_xiConv {μ : ℝ} (hμ : 0 < μ) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (-π) π) (α : ℝ) :
    HasSum (fun n : ℕ => π⁻¹ * Real.exp (-μ) ^ (n + 1) *
        (Real.cos (((n + 1 : ℕ) : ℝ) * α) * cosCoeff g (n + 1) +
          Real.sin (((n + 1 : ℕ) : ℝ) * α) * sinCoeff g (n + 1)))
      (xiConv μ g α - (2 * π)⁻¹ * cosCoeff g 0) := by
  let r := Real.exp (-μ)
  let a (n : ℕ) := 2 * r ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * α)
  let b (n : ℕ) := 2 * r ^ (n + 1) * Real.sin (((n + 1 : ℕ) : ℝ) * α)
  have hr := summable_geometric_of_lt_one (Real.exp_pos (-μ)).le (Real.exp_lt_one_iff.2 (by linarith : -μ < 0))
  have h (c : ℝ → ℝ) (hc : ∀ x, |c x| ≤ 1) :
      Summable (fun n : ℕ => 2 * r ^ (n + 1) * c (((n + 1 : ℕ) : ℝ) * α)) := by
    refine Summable.of_norm_bounded ((hr.mul_left r).mul_left 2) fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), ← pow_succ']
    exact mul_le_of_le_one_right (by positivity) (hc _)
  have hsum := hasSum_integral_trigTerm_mul (a := a) (b := b)
    (h _ Real.abs_cos_le_one) (h _ Real.abs_sin_le_one) hg fun β =>
      (hasSum_Xi_cos hμ (α - β)).congr_fun (fun n => by simp only [trigTerm, a, b]; rw [mul_sub, Real.cos_sub]; ring)
  have hsub : ∫ β in (-π)..π, (Xi μ (α - β) - 1) * g β =
      (∫ β in (-π)..π, Xi μ (α - β) * g β) - cosCoeff g 0 := by
    simpa [cosCoeff, sub_mul] using intervalIntegral.integral_sub (intervalIntegrable_Xi_mul hμ hg α) hg
  simp_rw [hsub, integral_trigTerm_mul a b _ hg] at hsum
  convert hsum.mul_left (2 * π)⁻¹ using 1
  · funext n
    dsimp [a, b, r]
    field_simp
  · unfold xiConv
    ring

theorem cosCoeff_zero (g : ℝ → ℝ) : cosCoeff g 0 = ∫ β in (-π)..π, g β := by
  simp [cosCoeff]

theorem integral_Xi_shift {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    (∫ β in (-π)..π, Xi μ (α - β)) = 2 * π := by
  have h := hasSum_xiConv hμ (g := fun _ => 1) intervalIntegrable_const α
  simp only [cosCoeff, sinCoeff, one_mul, integral_cos_nat_mul (Nat.succ_ne_zero _),
    integral_sin_nat_mul, mul_zero, add_zero] at h
  have hz := h.unique (hasSum_zero (α := ℝ) (β := ℕ))
  simp only [xiConv, mul_one, Nat.cast_zero, zero_mul, cos_zero, intervalIntegral.integral_const,
    smul_eq_mul] at hz
  field_simp at hz
  linarith

end PottsDiscontinuity.Bethe
