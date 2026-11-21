module

public import Mathlib.Analysis.MellinTransform

@[expose] public section

noncomputable section
open MeasureTheory

namespace DedekindZetaZeroFree.LargeSieve.InverseMellinBounds

private lemma uniform_complex_norm_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

private lemma uniform_norm_add_mul_I_le (c t v : ℝ) (hc0 : 0 ≤ c) (hcv : c ≤ v) (hv0 : 0 ≤ v) :
    ‖(c : ℂ) + (t : ℂ) * Complex.I‖ ≤ (v + 1) * (1 + |t|) := by
  calc ‖(c : ℂ) + (t : ℂ) * Complex.I‖
      ≤ ‖(c : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |c| + |t| := by
        rw [uniform_complex_norm_ofReal, norm_mul, uniform_complex_norm_ofReal,
          Complex.norm_I, mul_one]
    _ = c + |t| := by rw [abs_of_nonneg hc0]
    _ ≤ v + |t| := by linarith
    _ ≤ (v + 1) * (1 + |t|) := by nlinarith [abs_nonneg t, hv0]

private lemma uniform_abs_rpow_neg_two_le (t : ℝ) :
    (1 + |t|) ^ (-2 : ℝ) ≤ 2 * (1 + t ^ 2)⁻¹ := by
  rw [Real.rpow_neg (by positivity), Real.rpow_two, ← one_div, ← div_eq_mul_inv]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [abs_nonneg t, sq_abs t, sq_nonneg t]

private lemma uniform_integrable_one_add_abs_rpow_neg_two :
    Integrable (fun t : ℝ => (1 + |t|) ^ (-2 : ℝ)) := by
  simpa using (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp))

private lemma uniform_integral_one_add_abs_rpow_neg_two_le :
    ∫ t : ℝ, (1 + |t|) ^ (-2 : ℝ) ≤ 2 * Real.pi := by
  have h := integral_mono_of_nonneg (μ := volume)
    (Filter.Eventually.of_forall (fun t => Real.rpow_nonneg (by positivity) _))
    (integrable_inv_one_add_sq.const_mul 2)
    (Filter.Eventually.of_forall (fun t => uniform_abs_rpow_neg_two_le t))
  rwa [integral_const_mul, integral_univ_inv_one_add_sq] at h

private lemma uniform_rpow_pow_mul_inv (u : ℝ) (hu : 0 < u) (j : ℕ) :
    u ^ j * (u ^ (j + 2))⁻¹ = u ^ (-2 : ℝ) := by
  rw [← Real.rpow_natCast u j, ← Real.rpow_natCast u (j + 2), ← Real.rpow_neg hu.le,
    ← Real.rpow_add hu]
  push_cast
  ring_nf

private lemma uniform_jet_mul_bound (u : ℝ) (hu : 0 < u) (j : ℕ) (X Y : ℝ)
    (hXY : u ^ (j + 2) * Y ≤ X) :
    u ^ j * Y ≤ X * u ^ (-2 : ℝ) := by
  have hu2 : (0 : ℝ) < u ^ (j + 2) := by positivity
  have hY : Y ≤ X * (u ^ (j + 2))⁻¹ := by
    rw [le_mul_inv_iff₀ hu2, mul_comm]; exact hXY
  calc u ^ j * Y ≤ u ^ j * (X * (u ^ (j + 2))⁻¹) :=
        mul_le_mul_of_nonneg_left hY (by positivity)
    _ = X * (u ^ j * (u ^ (j + 2))⁻¹) := by ring
    _ = X * u ^ (-2 : ℝ) := by rw [uniform_rpow_pow_mul_inv u hu j]

private lemma uniform_norm_mellinInv_le (c x A : ℝ) (g : ℂ → ℂ) (hx : 0 < x) (hA : 0 ≤ A)
    (hbound : ∀ t : ℝ, ‖g (c + (t : ℂ) * Complex.I)‖ ≤ A * (1 + |t|) ^ (-2 : ℝ)) :
    ‖mellinInv c g x‖ ≤ A * x ^ (-c) := by
  set F : ℝ → ℂ := fun t => (x : ℂ) ^ (-(c + (t : ℂ) * Complex.I)) * g (c + (t : ℂ) * Complex.I)
    with hF
  have hFn : ∀ t, ‖F t‖ = x ^ (-c) * ‖g (c + (t : ℂ) * Complex.I)‖ := by
    intro t
    rw [hF, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    congr 1
    simp [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re]
  have hmaj_int : Integrable (fun t : ℝ => x ^ (-c) * A * (1 + |t|) ^ (-2 : ℝ)) := by
    have h := (uniform_integrable_one_add_abs_rpow_neg_two.const_mul (x ^ (-c) * A))
    simpa [mul_assoc] using h
  have hle : ∫ t, ‖F t‖ ≤ ∫ t, x ^ (-c) * A * (1 + |t|) ^ (-2 : ℝ) := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg (F t))) hmaj_int
    apply Filter.Eventually.of_forall
    intro t
    change ‖F t‖ ≤ x ^ (-c) * A * (1 + |t|) ^ (-2 : ℝ)
    rw [hFn t]
    have hxc : 0 ≤ x ^ (-c) := Real.rpow_nonneg hx.le _
    calc x ^ (-c) * ‖g (c + (t : ℂ) * Complex.I)‖
        ≤ x ^ (-c) * (A * (1 + |t|) ^ (-2 : ℝ)) := mul_le_mul_of_nonneg_left (hbound t) hxc
      _ = x ^ (-c) * A * (1 + |t|) ^ (-2 : ℝ) := by ring
  change ‖(1 / (2 * Real.pi) : ℝ) • ∫ t, F t‖ ≤ _
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  refine (mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm F).trans hle) (by positivity)).trans ?_
  rw [integral_const_mul]
  calc (1 / (2 * Real.pi)) * (x ^ (-c) * A * ∫ t, (1 + |t|) ^ (-2 : ℝ))
    _ ≤ (1 / (2 * Real.pi)) * (x ^ (-c) * A * (2 * Real.pi)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left uniform_integral_one_add_abs_rpow_neg_two_le
            (mul_nonneg (Real.rpow_nonneg hx.le _) hA)
        · positivity
    _ = A * x ^ (-c) := by field_simp

theorem euler_bound {c x A v : ℝ} {j q : ℕ} (g : ℂ → ℂ)
    (hx : 0 < x) (hA : 0 ≤ A) (hc : 0 ≤ c) (hcv : c ≤ v) (hq : q ≤ j)
    (hbound : ∀ t : ℝ, (1 + |t|) ^ (j + 2) * ‖g (c + (t : ℂ) * Complex.I)‖ ≤ A) :
    ‖mellinInv c (fun s => (-s)^q * g s) x‖ ≤ A * (v + 1)^j * x ^ (-c) := by
  have hv := hc.trans hcv
  apply uniform_norm_mellinInv_le c x _ _ hx (by positivity)
  intro t
  let s : ℂ := c + (t : ℂ) * Complex.I
  have hs : ‖s‖ ≤ (v + 1) * (1 + |t|) := uniform_norm_add_mul_I_le c t v hc hcv hv
  have hp := (pow_le_pow_left₀ (norm_nonneg s) hs q).trans
    (pow_le_pow_right₀ (show 1 ≤ (v+1)*(1+|t|) by nlinarith [abs_nonneg t]) hq)
  rw [mul_pow] at hp
  rw [norm_mul, norm_pow, norm_neg]
  calc ‖s‖ ^ q * ‖g s‖ ≤ (v + 1)^j * ((1 + |t|)^j * ‖g s‖) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ ≤ (v + 1)^j * (A * (1 + |t|)^(-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (uniform_jet_mul_bound _ (by positivity) j A _ (hbound t)) (by positivity)
    _ = _ := by ring

end DedekindZetaZeroFree.LargeSieve.InverseMellinBounds

end
