module
public import Mathlib

public import PottsDiscontinuity.Bethe.RatioProfile

/-! # Mean-value control of the singular logarithmic differences -/

@[expose] public section

open Set Finset


namespace PottsDiscontinuity.Bethe

theorem ratio_segment_distance {x y t : ℝ} (ht : t ∈ uIcc x y) :
    |t - x| ≤ |y - x| := abs_sub_left_of_mem_uIcc ht

theorem ratio_segment_away_zero {x y : ℝ} (hx : x ≠ 0) (hclose : |y - x| ≤ |x| / 2)
    {t : ℝ} (ht : t ∈ uIcc x y) : |x| / 2 ≤ |t| ∧ t ≠ 0 := by
  have hd := (ratio_segment_distance ht).trans hclose
  grind

/-- A mean-value bound on a segment that stays a fixed relative distance
from the singularity. This needs only a bound for `|t f'(t)|`. -/
theorem ratio_singular_difference_bound (f f' : ℝ → ℝ) {x y B : ℝ}
    (hx : x ≠ 0) (_hB : 0 ≤ B) (hclose : |y - x| ≤ |x| / 2)
    (hder : ∀ t ∈ uIcc x y, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ uIcc x y, |t * f' t| ≤ B) :
    |f y - f x| ≤  2 * B / |x|  * |y - x| := by
  have hxpos := abs_pos.mpr hx
  
  
  simpa only [Real.norm_eq_abs] using  Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
                                         (fun t ht => (hder t ht).hasDerivWithinAt) (fun (t : ℝ) (ht : t ∈ uIcc x y) => by
                                                                                       have htaway := (ratio_segment_away_zero hx hclose ht).1
                                                                                       have hb := hbound t ht
                                                                                       rw [abs_mul] at hb
                                                                                       rw [Real.norm_eq_abs]
                                                                                       apply (le_div_iff₀ hxpos).mpr
                                                                                       nlinarith) (convex_uIcc x y)
                                         left_mem_uIcc right_mem_uIcc 

/-- The actual spectral profile satisfies the relative-segment bound. -/
theorem ratio_ell_difference_bound {c x y : ℝ} (hc : 2 < c)
    (hx : x ∈ Ioo (-Real.pi) Real.pi) (hy : y ∈ Ioo (-Real.pi) Real.pi)
    (hx0 : x ≠ 0) (hclose : |y - x| ≤ |x| / 2) :
    |ratioEll c y - ratioEll c x| ≤
       2 * (Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi ^ 2 / 4) / |x|  * |y - x| := by
  
  have hseg : uIcc x y ⊆ Ioo (-Real.pi) Real.pi := by
    intro t ht
    rcases le_total x y with hxy | hyx
    · rw [uIcc_of_le hxy] at ht
      grind
    · rw [uIcc_of_ge hyx] at ht
      grind
  apply ratio_singular_difference_bound (ratioEll c) (ratioEllPrime c) hx0 (by
                                                                              bound) hclose
  · intro t ht
    exact ratio_hasDerivAt_ell hc (hseg ht) (ratio_segment_away_zero hx0 hclose ht).2
  · intro t ht
    exact ratio_ellPrime_weighted_bound hc (Ioo_subset_Icc_self (hseg ht))

/-- A displacement of size `C|x|/N` gives a uniformly `O(1/N)` log difference. -/
theorem ratio_scaled_ell_difference_bound {c x y C : ℝ} {N : ℕ}
    (hc : 2 < c) (hN : 0 < N) (hlarge : 2 * C ≤ N)
    (hx : x ∈ Ioo (-Real.pi) Real.pi) (hy : y ∈ Ioo (-Real.pi) Real.pi)
    (hx0 : x ≠ 0) (hshift : |y - x| ≤ C * |x| / N) :
    |(N : ℝ) * (ratioEll c y - ratioEll c x)| ≤
      2 * (Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi ^ 2 / 4) * C := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hxpos := abs_pos.mpr hx0
  
  
  let B := Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi ^ 2 / 4
  
  
  
  have he :  2 * B / |x|  * (C * |x| /  N ) =  2 * B * C  / N := by
    field_simp
  have hb  := (ratio_ell_difference_bound hc hx hy hx0 (by
                                                                     apply hshift.trans
                                                                     apply (div_le_iff₀ hNp).mpr
                                                                     nlinarith only [mul_le_mul_of_nonneg_right hlarge hxpos.le])).trans ((mul_le_mul_of_nonneg_left hshift (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (by
                                                                                                                                                                                                                                   bound)) hxpos.le)).trans_eq he)
  rw [abs_mul, abs_of_pos hNp]
  calc
    _ = |ratioEll c y - ratioEll c x| *  N  := mul_comm _ _
    _ ≤ 2 * B * C := (le_div_iff₀ hNp).mp hb

end PottsDiscontinuity.Bethe
