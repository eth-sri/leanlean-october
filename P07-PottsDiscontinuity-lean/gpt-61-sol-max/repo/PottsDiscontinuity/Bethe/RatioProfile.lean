module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.Scattering

/-! # The logarithmic spectral profile and its singular derivative

The value at zero is the total Lean value of the original spectral formula;
all differential assertions are on the punctured fundamental interval.
-/

@[expose] public section

open Set Complex


namespace PottsDiscontinuity.Bethe

open BetheAnsatz

/-- The source's `ℓ(x)=log |M(e^{ix})|`. -/
noncomputable def ratioEll (c x : ℝ)  := Real.log ‖M c (z x)‖

/-- Squared modulus of the numerator of `M`, in a manifestly positive form. -/
noncomputable def ratioNumerator (c x : ℝ) : ℝ :=
  (c ^ 2 - 2) ^ 2 + 2 * (c ^ 2 - 1) * (1 + Real.cos x)

/-- The classical derivative off zero, extended by its total rational value at zero. -/
noncomputable def ratioEllPrime (c x : ℝ) : ℝ :=
  -(c ^ 2 - 1) * Real.sin x / ratioNumerator c x -
    Real.sin x / (2 * (1 - Real.cos x))

theorem ratio_numerator_pos {c : ℝ} (hc : 2 < c) (x : ℝ) :
    0 < ratioNumerator c x := by
  have hc2 : 4 < c ^ 2 := by nlinarith
  
  
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (by linarith)) (mul_nonneg (by linarith) (by linarith [Real.neg_one_le_cos x]))

section

variable {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi)
include hx

theorem ratio_one_sub_cos_lower  :
    2 * x ^ 2 / Real.pi ^ 2 ≤ 1 - Real.cos x := by
  have hxhalf : |x / 2| ≤ Real.pi / 2 := by
    grind
  
  have hsq := (sq_le_sq₀ (by positivity) (abs_nonneg _)).mpr (Real.mul_abs_le_abs_sin hxhalf)
  
  rw [sq_abs] at hsq
  have hsin := Real.sin_sq_eq_half_sub (x / 2)
  rw [show 2 * (x / 2) = x by ring] at hsin
  
  field_simp at hsq
  rw [sq_abs, hsin] at hsq
  apply (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
  nlinarith only [hsq]

theorem ratio_one_sub_cos_pos  (hx0 : x ≠ 0) :
    0 < 1 - Real.cos x := lt_of_lt_of_le (by positivity )
                      (ratio_one_sub_cos_lower hx)

end

theorem ratio_normSq_M {c x : ℝ} (hx : z x ≠ 1) :
    Complex.normSq (M c (z x)) = ratioNumerator c x / (2 * (1 - Real.cos x)) := by
  
  
  rw [(by
         unfold M
         field_simp
         ring : M c (z x) = (1 - (c ) ^ 2 - z x) / (1 - z x)), Complex.normSq_div]
  have hz : z x = (Real.cos x : ℂ) + (Real.sin x : ℂ) * I := exp_I_mul_ofReal x
  rw [hz]
  
  simp only [Complex.normSq_apply, sub_re, sub_im, add_re, add_im, mul_re, mul_im, one_re, one_im, ofReal_re, ofReal_im, pow_two, I_re, I_im]
  unfold ratioNumerator
  congr 1 <;> nlinarith only [ Real.sin_sq_add_cos_sq x ]

section

variable {c x : ℝ} (hc : 2 < c) (hx : x ∈ Ioo (-Real.pi) Real.pi) (hx0 : x ≠ 0)
include hc hx hx0

theorem ratio_ell_eq_logs  :
    ratioEll c x = (1 / 2 : ℝ) * Real.log (ratioNumerator c x) -
      (1 / 2 : ℝ) * Real.log (2 * (1 - Real.cos x)) := by
  
  
  have hsq := ratio_normSq_M (c := c) (z_ne_one hx hx0)
  rw [Complex.normSq_eq_norm_sq] at hsq
  have hl := congrArg Real.log hsq
  rw [Real.log_div (ratio_numerator_pos hc x).ne' (mul_pos (by norm_num) (ratio_one_sub_cos_pos (Ioo_subset_Icc_self hx) hx0)).ne'] at hl
  norm_num at hl
  unfold ratioEll
  linarith only [hl]

theorem ratio_hasDerivAt_ell  :
    HasDerivAt (ratioEll c) (ratioEllPrime c x) x := by
  
  
  have hnum : HasDerivAt (ratioNumerator c) (-2 * (c ^ 2 - 1) * Real.sin x) x := by
    
    convert  (((Real.hasDerivAt_cos x).const_add 1).const_mul
               (2 * (c ^ 2 - 1))).const_add ((c ^ 2 - 2) ^ 2)  using 1
    all_goals aesop
  have hden : HasDerivAt (fun y => 2 * (1 - Real.cos y)) (2 * Real.sin x) x := by
    convert ((Real.hasDerivAt_cos x).const_sub 1).const_mul 2 using 1
    ring
  have h := ((hnum.log (ratio_numerator_pos hc x).ne').const_mul (1 / 2 )).sub
    ((hden.log (mul_pos (by norm_num) (ratio_one_sub_cos_pos (Ioo_subset_Icc_self hx) hx0)).ne').const_mul (1 / 2 ))
  have hder :  1 / 2  * ( -2 * (c ^ 2 - 1) * Real.sin x  / ratioNumerator c x) -
      (1 / 2 ) * ( 2 * Real.sin x  / (2 * (1 - Real.cos x))) = ratioEllPrime c x := by
    unfold ratioEllPrime
    ring
  have h' := h.congr_deriv hder
  apply h'.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2, eventually_ne_nhds hx0] with y hy hy0
  exact ratio_ell_eq_logs hc hy hy0

end

/-- A global bound for the derivative with its simple singularity removed. -/
theorem ratio_ellPrime_weighted_bound {c : ℝ} (hc : 2 < c)
    {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    |x * ratioEllPrime c x| ≤
      Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi ^ 2 / 4 := by
  have hc2 : 4 < c ^ 2 := by nlinarith
  
  have ha := ratio_numerator_pos hc x
  
  
  by_cases hx0 : x = 0
  · subst x
    simp only [zero_mul, abs_zero]
    exact add_nonneg (div_nonneg (mul_nonneg Real.pi_pos.le (by linarith)) (sq_pos_of_pos (by linarith)).le) (by positivity)
  have hd := ratio_one_sub_cos_pos hx hx0
  
  
  
  unfold ratioEllPrime
  rw [mul_sub]
  exact (abs_sub _ _).trans (add_le_add (by
                                           rw [abs_mul]
                                           calc
                                             _ ≤ Real.pi * ((c ^ 2 - 1) / (c ^ 2 - 2) ^ 2) :=
                                               mul_le_mul (by
                                                                                           grind) (by
                                                                   rw [abs_div, abs_mul, abs_neg, abs_of_pos ha, abs_of_pos (by linarith : 0 < c ^ 2 - 1)]
                                                                   calc
                                                                     _ ≤ (c ^ 2 - 1) / ratioNumerator c x := by
                                                                       apply div_le_div_of_nonneg_right _ ha.le
                                                                       nlinarith only [Real.abs_sin_le_one x, hc2]
                                                                     _ ≤ _ := div_le_div_of_nonneg_left (by linarith) (sq_pos_of_pos (by linarith)) (by
                                                                                                                                                       unfold ratioNumerator
                                                                                                                                                       have hs : 0 ≤ 2 * (c ^ 2 - 1) * (1 + Real.cos x) :=
                                                                                                                                                         mul_nonneg (by linarith) (by linarith [Real.neg_one_le_cos x])
                                                                                                                                                       linarith only [hs])) (abs_nonneg _) Real.pi_pos.le
                                             _ = _ := by ring) (by
                                                   rw [← mul_div_assoc, abs_div, abs_mul, abs_of_pos (mul_pos (by norm_num) hd)]
                                                   apply (div_le_iff₀ (mul_pos (by norm_num) hd)).mpr
                                                   have hsin : |x| * |Real.sin x| ≤ x ^ 2 := by
                                                     
                                                     simpa only [← pow_two, sq_abs] using (mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs (x := x)) (abs_nonneg x))
                                                   
                                                   apply hsin.trans
                                                   nlinarith only [ (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mp (ratio_one_sub_cos_lower hx) ]))

theorem ratio_continuousAt_ellPrime {c x : ℝ} (hc : 2 < c)
    (hx : x ∈ Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    ContinuousAt (ratioEllPrime c) x := by
  have hn  :=
    (ratio_numerator_pos hc x).ne'
  have hd  :=
    mul_ne_zero two_ne_zero (ratio_one_sub_cos_pos hx hx0).ne'
  unfold ratioEllPrime ratioNumerator
  fun_prop (disch := assumption)

end PottsDiscontinuity.Bethe
