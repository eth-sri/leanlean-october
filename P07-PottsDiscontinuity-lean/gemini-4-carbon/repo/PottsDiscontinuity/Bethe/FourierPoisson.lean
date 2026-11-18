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

@[expose] public section

open Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

/-- Poisson kernel series: `Ξ_μ(α) = 1 + 2 ∑_{m ≥ 1} e^{-μ m} cos(m α)` for `μ > 0`. -/
theorem hasSum_Xi_cos {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    HasSum (fun n : ℕ => 2 * Real.exp (-μ) ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * α))
      (Xi μ α - 1) := by
  set r := Real.exp (-μ) with hrdef
  have hr : 0 < r := Real.exp_pos _; have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hden : 0 < 1 - 2 * r * Real.cos α + r ^ 2 := by nlinarith [Real.cos_le_one α, sq_nonneg (1 - r), mul_pos hr hr]
  set z : ℂ := (r : ℂ) * Complex.exp (α * Complex.I) with hz
  have hz1 : ‖z‖ < 1 := by
    rw [hz, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs, abs_of_pos hr]; exact hr1
  have hre := (((Complex.hasSum_iff _ _).1 ((hasSum_geometric_of_norm_lt_one hz1).mul_left z)).1).mul_left 2
  have hterm (n : ℕ) : 2 * (z * z ^ n).re = 2 * r ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * α) := by
    rw [← pow_succ', hz, mul_pow, ← Complex.ofReal_pow, ← Complex.exp_nat_mul,
      show ((n + 1 : ℕ) : ℂ) * (α * Complex.I) = (((n + 1 : ℕ) : ℝ) * α : ℝ) * Complex.I by push_cast; ring,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]; ring
  have hzre : z.re = r * Real.cos α := by rw [hz, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hzim : z.im = r * Real.sin α := by rw [hz, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hs := Real.sin_sq_add_cos_sq α
  have hns : Complex.normSq (1 - z) = 1 - 2 * r * Real.cos α + r ^ 2 := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hzre, hzim]; simp; nlinarith [hs]
  have hval : 2 * (z * (1 - z)⁻¹).re = Xi μ α - 1 := by
    have hXi : Xi μ α - 1 = 2 * (r * Real.cos α - r ^ 2) / (1 - 2 * r * Real.cos α + r ^ 2) := by
      unfold Xi
      rw [Real.sinh_eq, Real.cosh_eq, ← hrdef, show Real.exp μ = r⁻¹ by rw [hrdef, Real.exp_neg, inv_inv],
        show (r⁻¹ + r) / 2 - Real.cos α = (1 - 2 * r * Real.cos α + r ^ 2) / (2 * r) by field_simp; ring,
        show (r⁻¹ - r) / 2 / ((1 - 2 * r * Real.cos α + r ^ 2) / (2 * r)) = (1 - r ^ 2) / (1 - 2 * r * Real.cos α + r ^ 2) by field_simp,
        div_sub_one hden.ne']
      congr 1; ring
    rw [hXi, Complex.mul_re, Complex.inv_re, Complex.inv_im, hns]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hzre, hzim]
    rw [← sub_eq_zero]; field_simp [hden.ne']; linear_combination -2 * r ^ 2 * hs
  simpa only [hterm, hval] using hre

theorem continuous_Xi {μ : ℝ} (hμ : 0 < μ) : Continuous (Xi μ) :=
  continuous_const.div (continuous_const.sub Real.continuous_cos) fun α => by
    linarith [Real.one_lt_cosh.mpr hμ.ne', Real.cos_le_one α]

private theorem integral_cos_int_mul {k : ℤ} (hk : k ≠ 0) : ∫ x in (-π)..π, Real.cos (k * x) = 0 := by
  rw [intervalIntegral.integral_comp_mul_left Real.cos (by exact_mod_cast hk), integral_cos]
  have h1 : Real.sin (k * π) = 0 := by exact_mod_cast Real.sin_int_mul_pi k
  rw [mul_neg, Real.sin_neg, h1]; simp

private theorem integral_sin_int_mul (k : ℤ) : ∫ x in (-π)..π, Real.sin (k * x) = 0 := by
  by_cases hk : k = 0; · simp [hk]
  rw [intervalIntegral.integral_comp_mul_left Real.sin (by exact_mod_cast hk), integral_sin, mul_neg, Real.cos_neg]; simp

theorem intervalIntegrable_cos_mul (k : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.cos (k * x)) volume (-π) π :=
  (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _

theorem intervalIntegrable_sin_mul (k : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.sin (k * x)) volume (-π) π :=
  (Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _

/-- Orthogonality: `∫_{-π}^{π} cos(m x) cos(n x) dx = π δ_{mn}` for `m, n ≥ 1`. -/
theorem integral_cos_mul_cos_pos {m n : ℕ} (_hm : m ≠ 0) (hn : n ≠ 0) :
    ∫ x in (-π)..π, Real.cos (m * x) * Real.cos (n * x) = if m = n then π else 0 := by
  have hid (x : ℝ) : Real.cos (m * x) * Real.cos (n * x) =
      (Real.cos ((((m : ℤ) - n : ℤ) : ℝ) * x) + Real.cos ((((m : ℤ) + n : ℤ) : ℝ) * x)) / 2 := by
    push_cast; rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]; ring
  simp_rw [hid]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (intervalIntegrable_cos_mul _) (intervalIntegrable_cos_mul _),
    integral_cos_int_mul (by omega : (m : ℤ) + n ≠ 0)]
  by_cases h : m = n
  · subst h; simp
  · rw [integral_cos_int_mul (by omega : (m : ℤ) - n ≠ 0)]; simp [h]

theorem integral_sin_mul_sin_pos {m n : ℕ} (_hm : m ≠ 0) (hn : n ≠ 0) :
    ∫ x in (-π)..π, Real.sin (m * x) * Real.sin (n * x) = if m = n then π else 0 := by
  have hid (x : ℝ) : Real.sin (m * x) * Real.sin (n * x) =
      (Real.cos ((((m : ℤ) - n : ℤ) : ℝ) * x) - Real.cos ((((m : ℤ) + n : ℤ) : ℝ) * x)) / 2 := by
    push_cast; rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]; ring
  simp_rw [hid]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (intervalIntegrable_cos_mul _) (intervalIntegrable_cos_mul _),
    integral_cos_int_mul (by omega : (m : ℤ) + n ≠ 0)]
  by_cases h : m = n
  · subst h; simp
  · rw [integral_cos_int_mul (by omega : (m : ℤ) - n ≠ 0)]; simp [h]

theorem integral_sin_mul_cos_nat (m n : ℕ) :
    ∫ x in (-π)..π, Real.sin (m * x) * Real.cos (n * x) = 0 := by
  have hid (x : ℝ) : Real.sin (m * x) * Real.cos (n * x) =
      (Real.sin ((((m : ℤ) + n : ℤ) : ℝ) * x) + Real.sin ((((m : ℤ) - n : ℤ) : ℝ) * x)) / 2 := by
    push_cast; rw [sub_mul, add_mul, Real.sin_sub, Real.sin_add]; ring
  simp_rw [hid]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (intervalIntegrable_sin_mul _) (intervalIntegrable_sin_mul _),
    integral_sin_int_mul, integral_sin_int_mul]; simp

theorem integral_cos_nat_mul {m : ℕ} (hm : m ≠ 0) : ∫ x in (-π)..π, Real.cos (m * x) = 0 := by
  simpa using integral_cos_int_mul (k := (m : ℤ)) (by exact_mod_cast hm)

theorem integral_sin_nat_mul (m : ℕ) : ∫ x in (-π)..π, Real.sin (m * x) = 0 := by
  simpa using integral_sin_int_mul (m : ℤ)

/-- `xiConv μ g α = (1/2π) ∫_{-π}^{π} Ξ_μ(α - β) g(β) dβ`. -/
noncomputable def xiConv (μ : ℝ) (g : ℝ → ℝ) (α : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ β in (-π)..π, Xi μ (α - β) * g β

/-- Cosine coefficient `∫_{-π}^{π} g(β) cos(m β) dβ` (unnormalised). -/
noncomputable def cosCoeff (g : ℝ → ℝ) (m : ℕ) : ℝ := ∫ β in (-π)..π, g β * Real.cos (m * β)

/-- Sine coefficient `∫_{-π}^{π} g(β) sin(m β) dβ` (unnormalised). -/
noncomputable def sinCoeff (g : ℝ → ℝ) (m : ℕ) : ℝ := ∫ β in (-π)..π, g β * Real.sin (m * β)

theorem cosCoeff_zero (g : ℝ → ℝ) : cosCoeff g 0 = ∫ β in (-π)..π, g β := by simp [cosCoeff]

theorem hasSum_xiConv {μ : ℝ} (hμ : 0 < μ) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (-π) π) (α : ℝ) :
    HasSum (fun n : ℕ => π⁻¹ * Real.exp (-μ) ^ (n + 1) *
        (Real.cos (((n + 1 : ℕ) : ℝ) * α) * cosCoeff g (n + 1) +
          Real.sin (((n + 1 : ℕ) : ℝ) * α) * sinCoeff g (n + 1)))
      (xiConv μ g α - (2 * π)⁻¹ * cosCoeff g 0) := by
  have hpi := Real.pi_pos
  set r := Real.exp (-μ)
  have hr : 0 < r := Real.exp_pos _; have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  let F (n : ℕ) (β : ℝ) := 2 * r ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * (α - β)) * g β
  have hgi : IntegrableOn g (Ioc (-π) π) volume := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1 hg
  have hgeo : Summable (fun n : ℕ => 2 * r ^ (n + 1)) :=
    ((summable_geometric_of_lt_one hr.le hr1).mul_left (2 * r)).congr fun _ => by ring
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := -π) (b := π) (F := F) (f := fun β => (Xi μ (α - β) - 1) * g β)
    (fun n β => 2 * r ^ (n + 1) * ‖g β‖)
    (fun n => by rw [uIoc_of_le (by linarith)]; exact (Continuous.aestronglyMeasurable (by fun_prop)).mul hgi.aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun β _ => by
      dsimp [F]
      rw [mul_assoc, abs_mul, abs_mul, abs_mul, abs_of_pos two_pos, abs_of_nonneg (by positivity : 0 ≤ r ^ (n + 1))]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)) (by positivity))
    (Filter.Eventually.of_forall fun _ _ => hgeo.mul_right _)
    (by simp_rw [tsum_mul_right]; exact hg.norm.const_mul _)
    (Filter.Eventually.of_forall fun β _ => (hasSum_Xi_cos hμ (α - β)).mul_right (g β))
  have hI (n : ℕ) : ∫ β in (-π)..π, F n β =
      2 * r ^ (n + 1) * (Real.cos (((n + 1 : ℕ) : ℝ) * α) * cosCoeff g (n + 1) +
        Real.sin (((n + 1 : ℕ) : ℝ) * α) * sinCoeff g (n + 1)) := by
    have h1 (β : ℝ) : F n β = 2 * r ^ (n + 1) *
        (Real.cos (((n + 1 : ℕ) : ℝ) * α) * (g β * Real.cos (((n + 1 : ℕ) : ℝ) * β)) +
          Real.sin (((n + 1 : ℕ) : ℝ) * α) * (g β * Real.sin (((n + 1 : ℕ) : ℝ) * β))) := by
      dsimp [F]; rw [mul_sub, Real.cos_sub]; ring
    simp_rw [h1]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      ((hg.mul_continuousOn (by fun_prop)).const_mul _) ((hg.mul_continuousOn (by fun_prop)).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]; rfl
  simp_rw [hI] at hsum
  have hXg : IntervalIntegrable (fun β => Xi μ (α - β) * g β) volume (-π) π :=
    hg.continuousOn_mul ((continuous_Xi hμ).comp (by fun_prop)).continuousOn
  have hsplit : ∫ β in (-π)..π, (Xi μ (α - β) - 1) * g β = (∫ β in (-π)..π, Xi μ (α - β) * g β) - cosCoeff g 0 := by
    rw [show (fun β => (Xi μ (α - β) - 1) * g β) = fun β => Xi μ (α - β) * g β - g β by funext; ring,
      intervalIntegral.integral_sub hXg hg, cosCoeff_zero]
  rw [hsplit] at hsum
  convert hsum.mul_left (2 * π)⁻¹ using 1
  · funext n; field_simp
  · unfold xiConv; ring

private noncomputable def xiConvTerm (μ : ℝ) (g : ℝ → ℝ) (n : ℕ) (α : ℝ) : ℝ :=
  π⁻¹ * Real.exp (-μ) ^ (n + 1) *
    (Real.cos (((n + 1 : ℕ) : ℝ) * α) * cosCoeff g (n + 1) +
      Real.sin (((n + 1 : ℕ) : ℝ) * α) * sinCoeff g (n + 1))

private theorem abs_xiConvTerm_le {μ : ℝ} {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-π) π)
    (n : ℕ) (α : ℝ) :
    |xiConvTerm μ g n α| ≤ π⁻¹ * Real.exp (-μ) ^ (n + 1) * (2 * ∫ β in (-π)..π, |g β|) := by
  have hpi := Real.pi_pos
  let L := ∫ β in (-π)..π, |g β|
  have htrig {f : ℝ → ℝ} (hf : Continuous f) (hb : ∀ x, |f x| ≤ 1) : |∫ β in (-π)..π, g β * f β| ≤ L :=
    (intervalIntegral.abs_integral_le_integral_abs (by linarith)).trans <|
      intervalIntegral.integral_mono_on (by linarith) (hg.mul_continuousOn hf.continuousOn).abs hg.abs fun β _ => by
        rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hb β)
  have h1 : |cosCoeff g (n + 1)| ≤ L := htrig (by fun_prop) fun _ => Real.abs_cos_le_one _
  have h2 : |sinCoeff g (n + 1)| ≤ L := htrig (by fun_prop) fun _ => Real.abs_sin_le_one _
  unfold xiConvTerm
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ π⁻¹ * Real.exp (-μ) ^ (n + 1))]
  refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) (by positivity)
  rw [abs_mul, abs_mul]
  linarith [mul_le_of_le_one_left (abs_nonneg (cosCoeff g (n + 1))) (Real.abs_cos_le_one (((n + 1 : ℕ) : ℝ) * α)),
    mul_le_of_le_one_left (abs_nonneg (sinCoeff g (n + 1))) (Real.abs_sin_le_one (((n + 1 : ℕ) : ℝ) * α))]

/-- Uniqueness mechanism: if `D` is integrable and `D = -(Ξ_μ * D)` on `(-π, π]`, then `D = 0`
almost everywhere on `(-π, π]`. -/
theorem eq_zero_of_eq_neg_xiConv {μ : ℝ} (hμ : 0 < μ) {D : ℝ → ℝ}
    (hD : IntervalIntegrable D volume (-π) π)
    (h : ∀ α ∈ Ioc (-π) π, D α = -xiConv μ D α) :
    D =ᵐ[volume.restrict (Ioc (-π) π)] 0 := by
  have hpi := Real.pi_pos
  have hr : 0 < Real.exp (-μ) := Real.exp_pos _
  have hr1 : Real.exp (-μ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  let L := ∫ β in (-π)..π, |D β|
  let A := (2 * π)⁻¹ * cosCoeff D 0
  have hsBound (C : ℝ) : Summable (fun n : ℕ => π⁻¹ * Real.exp (-μ) ^ (n + 1) * C) :=
    ((summable_geometric_of_lt_one hr.le hr1).mul_left (π⁻¹ * Real.exp (-μ) * C)).congr fun _ => by ring
  have hcont : Continuous (xiConv μ D) := by
    rw [show xiConv μ D = fun α => A + ∑' n : ℕ, xiConvTerm μ D n α from
      funext fun α => by have := (hasSum_xiConv hμ hD α).tsum_eq; unfold xiConvTerm; linarith]
    exact continuous_const.add (continuous_tsum (fun n => by unfold xiConvTerm; fun_prop)
      (hsBound (2 * L)) (fun n α => abs_xiConvTerm_le hD n α))
  have hDi : IntegrableOn D (Ioc (-π) π) volume := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1 hD
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := -π) (b := π) (F := fun n α => D α * xiConvTerm μ D n α)
    (f := fun α => D α * (xiConv μ D α - A))
    (fun n α => |D α| * (π⁻¹ * Real.exp (-μ) ^ (n + 1) * (2 * L)))
    (fun n => by rw [uIoc_of_le (by linarith)]; exact hDi.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by unfold xiConvTerm; fun_prop)))
    (fun n => Filter.Eventually.of_forall fun α _ => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_xiConvTerm_le hD n α) (abs_nonneg _))
    (Filter.Eventually.of_forall fun _ _ => (hsBound (2 * L)).mul_left _)
    (by simp_rw [tsum_mul_left]; exact hD.abs.mul_const _)
    (Filter.Eventually.of_forall fun α _ => (hasSum_xiConv hμ hD α).mul_left (D α))
  have hterm (n : ℕ) : ∫ α in (-π)..π, D α * xiConvTerm μ D n α =
      π⁻¹ * Real.exp (-μ) ^ (n + 1) * (cosCoeff D (n + 1) ^ 2 + sinCoeff D (n + 1) ^ 2) := by
    have h1 (α : ℝ) : D α * xiConvTerm μ D n α = π⁻¹ * Real.exp (-μ) ^ (n + 1) *
        (cosCoeff D (n + 1) * (D α * Real.cos (((n + 1 : ℕ) : ℝ) * α)) +
          sinCoeff D (n + 1) * (D α * Real.sin (((n + 1 : ℕ) : ℝ) * α))) := by unfold xiConvTerm; ring
    simp_rw [h1]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      ((hD.mul_continuousOn (by fun_prop)).const_mul _) ((hD.mul_continuousOn (by fun_prop)).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    change π⁻¹ * Real.exp (-μ) ^ (n + 1) * (cosCoeff D (n + 1) * cosCoeff D (n + 1) + sinCoeff D (n + 1) * sinCoeff D (n + 1)) = _
    ring
  simp_rw [hterm] at hsum
  have hnn : 0 ≤ ∫ α in (-π)..π, D α * xiConv μ D α := by
    have hgx : IntervalIntegrable (fun α => D α * (xiConv μ D α - A)) volume (-π) π :=
      hD.mul_continuousOn (Continuous.continuousOn (by fun_prop))
    rw [show (fun α => D α * xiConv μ D α) = fun α => D α * A + D α * (xiConv μ D α - A) by funext; ring,
      intervalIntegral.integral_add (hD.mul_const A) hgx,
      intervalIntegral.integral_mul_const, ← cosCoeff_zero D]
    have hA0 : 0 ≤ cosCoeff D 0 * A := by dsimp [A]; nlinarith [mul_self_nonneg (cosCoeff D 0), inv_pos.mpr (mul_pos two_pos hpi)]
    linarith [hsum.nonneg fun _ => by positivity]
  rw [intervalIntegral.integral_of_le (by linarith)] at hnn
  have hEi : IntegrableOn (fun α => D α * xiConv μ D α) (Ioc (-π) π) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1 (hD.mul_continuousOn hcont.continuousOn)
  have hsq : ∀ᵐ α ∂(volume.restrict (Ioc (-π) π)), D α ^ 2 = -(D α * xiConv μ D α) := by
    filter_upwards [(ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall h)] with α hα
    conv_lhs => rw [sq]; arg 2; rw [hα]
    ring
  have hint : ∫ α in Ioc (-π) π, D α ^ 2 = -∫ α in Ioc (-π) π, D α * xiConv μ D α :=
    (integral_congr_ae hsq).trans (MeasureTheory.integral_neg _)
  have h0 : ∫ α in Ioc (-π) π, D α ^ 2 = 0 :=
    le_antisymm (by linarith) (setIntegral_nonneg measurableSet_Ioc fun α _ => sq_nonneg (D α))
  filter_upwards [(integral_eq_zero_iff_of_nonneg (fun α => sq_nonneg (D α))
    (hEi.neg.congr (by filter_upwards [hsq] with _ hα; exact hα.symm))).1 h0] with α hα
  simpa using hα

end PottsDiscontinuity.Bethe
