module

public import PottsDiscontinuity.Bethe.RatioProfile

/-! # Mean-value control of the singular logarithmic differences -/

@[expose] public section

open Set Finset
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

theorem ratio_segment_away_zero {x y : ℝ} (hx : x ≠ 0) (hclose : |y - x| ≤ |x| / 2)
    {t : ℝ} (ht : t ∈ uIcc x y) : |x| / 2 ≤ |t| ∧ t ≠ 0 := by
  have hd := (abs_sub_left_of_mem_uIcc ht).trans hclose
  grind

/-- A mean-value bound on a segment that stays a fixed relative distance
from the singularity. This needs only a bound for `|t f'(t)|`. -/
theorem ratio_singular_difference_bound (f f' : ℝ → ℝ) {x y B : ℝ}
    (hx : x ≠ 0) (hclose : |y - x| ≤ |x| / 2)
    (hder : ∀ t ∈ uIcc x y, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ uIcc x y, |t * f' t| ≤ B) :
    |f y - f x| ≤ (2 * B / |x|) * |y - x| := by
  have hxpos := abs_pos.mpr hx
  have hderbound (t : ℝ) (ht : t ∈ uIcc x y) : ‖f' t‖ ≤ 2 * B / |x| := by
    have htaway := (ratio_segment_away_zero hx hclose ht).1
    have hb := hbound t ht
    rw [abs_mul] at hb
    rw [Real.norm_eq_abs]
    apply (le_div_iff₀ hxpos).mpr
    have hm := mul_le_mul_of_nonneg_right htaway (abs_nonneg (f' t))
    nlinarith only [hm, hb]
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hder t ht).hasDerivWithinAt) hderbound (convex_uIcc x y)
    (left_mem_uIcc : x ∈ uIcc x y) (right_mem_uIcc : y ∈ uIcc x y)
  assumption

/-- The actual spectral profile satisfies the relative-segment bound. -/
theorem ratio_ell_difference_bound {c x y : ℝ} (hc : 2 < c)
    (hx : x ∈ Ioo (-Real.pi) Real.pi) (hy : y ∈ Ioo (-Real.pi) Real.pi)
    (hx0 : x ≠ 0) (hclose : |y - x| ≤ |x| / 2) :
    |ratioEll c y - ratioEll c x| ≤
      (2 * (Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi ^ 2 / 4) / |x|) * |y - x| := by
  have hseg : uIcc x y ⊆ Ioo (-Real.pi) Real.pi := ordConnected_Ioo.uIcc_subset hx hy
  apply ratio_singular_difference_bound (ratioEll c) (ratioEllPrime c) hx0 hclose
  · intro t ht
    exact ratio_hasDerivAt_ell hc (hseg ht) (ratio_segment_away_zero hx0 hclose ht).2
  · intro t ht
    exact ratio_ellPrime_weighted_bound hc (Ioo_subset_Icc_self (hseg ht))

theorem ratio_profile_bound_nonneg {c : ℝ} (hc : 2 < c) :
    0 ≤ Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi ^ 2 / 4 :=
  (abs_nonneg _).trans (ratio_ellPrime_weighted_bound hc (x := 0) (by simp [Real.pi_nonneg]))

theorem ratio_scaled_root_log_bound {c x y C : ℝ} {N : ℕ}
    (hc : 2 < c) (hN : 0 < N) (hC : 0 ≤ C) (hlarge : 2 * C ≤ N)
    (hx : x ∈ Ioo (-Real.pi) Real.pi) (hy : y ∈ Ioo (-Real.pi) Real.pi)
    (hshift : |(N : ℝ) * (x - y)| ≤ C * |x|) :
    |(N : ℝ) * (ratioEll c x - ratioEll c y)| ≤
      2 * (Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi ^ 2 / 4) * C := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let B := Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi ^ 2 / 4
  have hB : 0 ≤ B := ratio_profile_bound_nonneg hc
  rw [abs_mul, abs_of_pos hNp, abs_sub_comm] at hshift
  by_cases hx0 : x = 0
  · have hs : (N : ℝ) * |y - x| ≤ 0 := by simpa only [hx0, abs_zero, mul_zero] using hshift
    have hxy := sub_eq_zero.mp (abs_nonpos_iff.mp (nonpos_of_mul_nonpos_right hs hNp))
    rw [hxy, sub_self, mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hB) hC
  have hsmall := (le_div_iff₀' hNp).mpr hshift
  have hhalf : |y - x| ≤ |x| / 2 := hsmall.trans ((div_le_iff₀ hNp).mpr
    (by nlinarith only [mul_le_mul_of_nonneg_right hlarge (abs_nonneg x)]))
  have h := ratio_ell_difference_bound hc hx hy hx0 hhalf
  rw [abs_mul, abs_of_pos hNp, abs_sub_comm]
  calc
    _ ≤ (N : ℝ) * (2 * B / |x| * |y - x|) := mul_le_mul_of_nonneg_left h hNp.le
    _ = (2 * B / |x|) * ((N : ℝ) * |y - x|) := by ring
    _ ≤ (2 * B / |x|) * (C * |x|) := mul_le_mul_of_nonneg_left hshift (by positivity)
    _ = 2 * B * C := by field_simp [abs_ne_zero.mpr hx0]

end PottsDiscontinuity.Bethe
