module
public import Mathlib

public import PottsDiscontinuity.Bethe.RatioSecondDerivative

/-! # Summable bounds for the logarithms of odd midpoint factors -/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

theorem ratio_midpoint_second_difference (f f' f'' : ℝ → ℝ) {a b L : ℝ}
    (hab : a ≤ b) (hL : 0 ≤ L)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc a b, HasDerivAt f' (f'' x) x)
    (hbound : ∀ x ∈ Icc a b, |f'' x| ≤ L) :
    |2 * f ((a + b) / 2) - f a - f b| ≤ L * (b - a) ^ 2 := by
  let m := (a + b) / 2
  have hm : m ∈ Icc a b := by dsimp [m]; constructor <;> linarith
  
  let g  := fun x => f x - f' m * x
  have hg (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt g (f' x - f' m) x := by
    simpa only [mul_one] using!
      (hf x hx).sub ((hasDerivAt_id x).const_mul (f' m))
  
  have hgLip (x : ℝ) (hx : x ∈ Icc a b) : |g x - g m| ≤ L * (b - a) * |x - m| := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun y hy => HasDerivAt.hasDerivWithinAt (hg y hy)) (fun (x : ℝ) (hx : x ∈ Icc a b) => by
                                                                                                                                                                                           apply ((fun u hu v hv => Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun x hx => HasDerivAt.hasDerivWithinAt (hf' x hx)) hbound
                                                                                                                                                                                                                                        (convex_Icc a b) hu hv) m hm x hx).trans
                                                                                                                                                                                           apply mul_le_mul_of_nonneg_left _ hL
                                                                                                                                                                                           apply abs_le.mpr
                                                                                                                                                                                           constructor <;> linarith [hx.1, hx.2, hm.1, hm.2])
                                                                                   (convex_Icc a b) hm hx
  have ha := hgLip a ⟨le_rfl, hab⟩
  have hb := hgLip b ⟨hab, le_rfl⟩
  
  have hbm : |b - m| = (b - a) / 2 := by
    grind
  rw [(by
         grind : |a - m| = (b - a) / 2)] at ha
  rw [hbm] at hb
  
  
  rw [(by
         
         ring : 2 * f m - f a - f b = -(g a - g m) - (g b - g m))]
  have htri := abs_sub (-(g a - g m)) (g b - g m)
  rw [abs_neg] at htri
  nlinarith only [ha, hb, htri]

theorem ratio_midpoint_log_bound {c : ℝ} (hc : 2 < c) :
    ∃ B ≥ 0, ∀ a b : ℝ, 0 < a → a ≤ b → b < Real.pi →
      |2 * ratioEll c ((a + b) / 2) - ratioEll c a - ratioEll c b| ≤
        B * ((b - a) / a) ^ 2 := by
  obtain ⟨B, hB, hbnd⟩ := ratio_ellSecond_weighted_bound hc
  refine ⟨B, hB, ?_⟩
  intro a b ha hab hb
  have hInt (x : ℝ) (hx : x ∈ Icc a b) : x ∈ Ioo (-Real.pi) Real.pi := by
    grind
  have hxpos (x : ℝ) (hx : x ∈ Icc a b)  := ha.trans_le hx.1
  
   
  
  exact (ratio_midpoint_second_difference (ratioEll c) (ratioEllPrime c) (ratioEllSecond c)
           hab (div_nonneg hB (sq_nonneg a))
           (fun x hx => ratio_hasDerivAt_ell hc (hInt x hx) (hxpos x hx).ne')
           (fun x hx => ratio_hasDerivAt_ellPrime hc (Ioo_subset_Icc_self (hInt x hx)) (hxpos x hx).ne')
            fun x hx => by
              have ht := hbnd x (Ioo_subset_Icc_self (hInt x hx))
              rw [abs_mul, abs_of_nonneg (sq_nonneg x)] at ht
              have hax  := (sq_le_sq₀ ha.le (hxpos x hx).le).mpr hx.1
              have hm := mul_le_mul_of_nonneg_right hax (abs_nonneg (ratioEllSecond c x))
              apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
              nlinarith only [ht, hm]).trans_eq (by ring)

/-- The spatial mesh and positive-rank separation turn the previous estimate
into a summable reciprocal-square bound, uniform in N and the rank. -/
theorem ratio_midpoint_rank_bound {c B M D a b : ℝ} {N k : ℕ}
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hD : 0 ≤ D) (hN : 0 < N)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi)
    (hprofile : ∀ u v : ℝ, 0 < u → u ≤ v → v < Real.pi →
      |2 * ratioEll c ((u + v) / 2) - ratioEll c u - ratioEll c v| ≤ B * ((v - u) / u) ^ 2)
    (hgap : b - a ≤ D / N) (hrank : (k : ℝ) + 1 / 2 ≤  M * N  * a) :
    |2 * ratioEll c ((a + b) / 2) - ratioEll c a - ratioEll c b| ≤
       B * (2 * M * D) ^ 2  / ((k : ℝ) + 1) ^ 2 := by
  
  have hkpos :  0  < (k : ℝ) + 1 := by positivity
  have hrank' :  k  + 1 ≤ 2 * (M * N) * a := by
    linarith
  
  have h₁ := mul_le_mul_of_nonneg_right hrank' (sub_nonneg.mpr hab)
  have h₂ := mul_le_mul_of_nonneg_left ((le_div_iff₀ (Nat.cast_pos.mpr hN)).mp hgap) (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM) ha.le)
  have hratio : (b - a) / a ≤  2 * M * D  / ( k  + 1) := by
    apply (div_le_div_iff₀ ha hkpos).mpr
    all_goals grind
  have hsquare  :=
    (sq_le_sq₀ (div_nonneg (sub_nonneg.mpr hab) ha.le) (by positivity)).mpr hratio
  apply (hprofile a b ha hab hb).trans
  
  exact (mul_le_mul_of_nonneg_left hsquare hB).trans_eq (by rw [div_pow, ← mul_div_assoc])

end PottsDiscontinuity.Bethe
