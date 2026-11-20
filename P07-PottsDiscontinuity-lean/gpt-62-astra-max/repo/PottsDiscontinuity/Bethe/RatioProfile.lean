module

public import PottsDiscontinuity.BetheAnsatz.Scattering

/-! # The logarithmic spectral profile and its singular derivative

The value at zero is the total Lean value of the original spectral formula;
all differential assertions are on the punctured fundamental interval.
-/

@[expose] public section

open Set Complex
open scoped Topology

namespace PottsDiscontinuity.Bethe

open BetheAnsatz

section
variable (c x : ℝ)
include c x

/-- The source's `ℓ(x)=log |M(e^{ix})|`. -/
noncomputable def ratioEll : ℝ := Real.log ‖M c (z x)‖

/-- Squared modulus of the numerator of `M`, in a manifestly positive form. -/
noncomputable def ratioNumerator : ℝ :=
  (c ^ 2 - 2) ^ 2 + 2 * (c ^ 2 - 1) * (1 + Real.cos x)

/-- The classical derivative off zero, extended by its total rational value at zero. -/
noncomputable def ratioEllPrime : ℝ :=
  -(c ^ 2 - 1) * Real.sin x / ratioNumerator c x -
    Real.sin x / (2 * (1 - Real.cos x))

end

theorem ratio_numerator_pos {c : ℝ} (hc : 2 < c) (x : ℝ) :
    0 < ratioNumerator c x := by
  have hc2 : 4 < c ^ 2 := by nlinarith
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (by linarith)) (mul_nonneg (by linarith) (by linarith [Real.neg_one_le_cos x]))

section
variable {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi)
include hx

theorem ratio_one_sub_cos_lower :
    2 * x ^ 2 / Real.pi ^ 2 ≤ 1 - Real.cos x := by
  have hxhalf : |x / 2| ≤ Real.pi / 2 := by
    grind
  have hsq := (sq_le_sq₀ (by positivity) (abs_nonneg _)).mpr (Real.mul_abs_le_abs_sin hxhalf)
  have habs : |x / 2| = |x| / 2 := by simp [abs_div]
  rw [habs, mul_pow, div_pow, sq_abs] at hsq
  have hsin := Real.sin_sq_eq_half_sub (x / 2)
  rw [show 2 * (x / 2) = x by ring] at hsin
  field_simp at hsq
  rw [sq_abs, hsin] at hsq
  apply (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
  linarith

theorem ratio_one_sub_cos_pos (hx0 : x ≠ 0) :
    0 < 1 - Real.cos x := lt_of_lt_of_le (by positivity)
    (ratio_one_sub_cos_lower hx)

end

variable {c x : ℝ} (hc : 2 < c) (hx : x ∈ Ioo (-Real.pi) Real.pi) (hx0 : x ≠ 0)

theorem ratio_normSq_M (hx : z x ≠ 1) :
    Complex.normSq (M c (z x)) = ratioNumerator c x / (2 * (1 - Real.cos x)) := by
  have hM : M c (z x) = (1 - c ^ 2 - z x) / (1 - z x) := by
    unfold M
    field_simp
    ring
  rw [hM, Complex.normSq_div]
  have hz : z x = (Real.cos x) + (Real.sin x) * I := exp_I_mul_ofReal x
  rw [hz]
  have hsin := Real.sin_sq_add_cos_sq x
  simp only [Complex.normSq_apply, sub_re, sub_im, add_re, add_im, mul_re, mul_im,
    one_re, one_im, ofReal_re, ofReal_im, pow_two, I_re, I_im, mul_zero, zero_mul,
    mul_one, zero_add, add_zero, sub_zero, zero_sub]
  grind [ratioNumerator]

include hc hx hx0 in
theorem ratio_ell_eq_logs :
    ratioEll c x = (1 / 2) * Real.log (ratioNumerator c x) -
      (1 / 2) * Real.log (2 * (1 - Real.cos x)) := by
  have hsq := ratio_normSq_M (c := c) (z_ne_one hx hx0)
  rw [Complex.normSq_eq_norm_sq] at hsq
  have hl := congrArg Real.log hsq
  rw [Real.log_pow, Real.log_div (ratio_numerator_pos hc x).ne' (mul_pos (by norm_num) (ratio_one_sub_cos_pos (Ioo_subset_Icc_self hx) hx0)).ne'] at hl
  grind [ratioEll]

include hc hx hx0 in
theorem ratio_hasDerivAt_ell :
    HasDerivAt (ratioEll c) (ratioEllPrime c x) x := by
  have hnum : HasDerivAt (ratioNumerator c) (-2 * (c ^ 2 - 1) * Real.sin x) x := by
    convert ((((Real.hasDerivAt_cos x).const_add 1).const_mul (2 * (c ^ 2 - 1))).const_add ((c ^ 2 - 2) ^ 2)) using 1
    · rfl
    · ring
  have hden : HasDerivAt (fun y => 2 * (1 - Real.cos y)) (2 * Real.sin x) x := by
    convert ((Real.hasDerivAt_cos x).const_sub 1).const_mul 2 using 1
    ring
  have h := ((hnum.log (ratio_numerator_pos hc x).ne').const_mul (1 / 2)).sub
    ((hden.log (mul_pos (by norm_num) (ratio_one_sub_cos_pos (Ioo_subset_Icc_self hx) hx0)).ne').const_mul (1 / 2))
  have hder : (1 / 2) * ((-2 * (c ^ 2 - 1) * Real.sin x) / ratioNumerator c x) -
      (1 / 2) * ((2 * Real.sin x) / (2 * (1 - Real.cos x))) = ratioEllPrime c x := by
    unfold ratioEllPrime
    ring
  apply (h.congr_deriv hder).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2, eventually_ne_nhds hx0] with y hy hy0
  exact ratio_ell_eq_logs hc hy hy0

/-- A global bound for the derivative with its simple singularity removed. -/
theorem ratio_ellPrime_weighted_bound {c : ℝ} (hc : 2 < c)
    {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    |x * ratioEllPrime c x| ≤
      Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi ^ 2 / 4 := by
  have hc2 : 4 < c ^ 2 := by nlinarith
  have ha0 : 0 < (c ^ 2 - 2) ^ 2 := sq_pos_of_pos (by linarith)
  have ha := ratio_numerator_pos hc x
  have hxabs := abs_le.mpr ⟨by grind, hx.2⟩
  by_cases hx0 : x = 0
  · subst x
    simp only [zero_mul, abs_zero]
    exact add_nonneg (div_nonneg (mul_nonneg Real.pi_pos.le (by linarith)) ha0.le) (by positivity)
  have hd := ratio_one_sub_cos_pos hx hx0
  have hfirst : |-(c ^ 2 - 1) * Real.sin x / ratioNumerator c x| ≤
      (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 := by
    rw [abs_div, abs_mul, abs_neg, abs_of_pos ha, abs_of_pos (by linarith)]
    calc
      _ ≤ (c ^ 2 - 1) / ratioNumerator c x := by
        apply div_le_div_of_nonneg_right _ ha.le
        nlinarith only [Real.abs_sin_le_one x, hc2]
      _ ≤ _ := div_le_div_of_nonneg_left (by linarith) ha0 (by
        unfold ratioNumerator
        have hs : 0 ≤ 2 * (c ^ 2 - 1) * (1 + Real.cos x) :=
          mul_nonneg (by linarith) (by linarith [Real.neg_one_le_cos x])
        linarith)
  unfold ratioEllPrime
  rw [mul_sub]
  exact (abs_sub _ _).trans (add_le_add (by
    rw [abs_mul]
    calc
      _ ≤ Real.pi * ((c ^ 2 - 1) / (c ^ 2 - 2) ^ 2) :=
        mul_le_mul hxabs hfirst (abs_nonneg _) Real.pi_pos.le
      _ = _ := by ring) (by
    rw [← mul_div_assoc, abs_div, abs_mul, abs_of_pos (mul_pos (by norm_num) hd)]
    apply (div_le_iff₀ (mul_pos (by norm_num) hd)).mpr
    have hsin : |x| * |Real.sin x| ≤ x ^ 2 := by
      have ht := mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs (x := x)) (abs_nonneg x)
      simpa only [← pow_two, sq_abs] using ht
    have hcos := (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mp (ratio_one_sub_cos_lower hx)
    linarith))

include hc in
theorem ratio_continuousAt_ellPrime
    (hx : x ∈ Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    ContinuousAt (ratioEllPrime c) x := by
  have hn : (c ^ 2 - 2) ^ 2 + 2 * (c ^ 2 - 1) * (1 + Real.cos x) ≠ 0 :=
    (ratio_numerator_pos hc x).ne'
  have hd :=
    mul_ne_zero two_ne_zero (ratio_one_sub_cos_pos hx hx0).ne'
  unfold ratioEllPrime ratioNumerator
  fun_prop

end PottsDiscontinuity.Bethe
