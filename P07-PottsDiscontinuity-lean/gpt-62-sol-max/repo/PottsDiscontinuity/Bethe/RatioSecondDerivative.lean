module

public import PottsDiscontinuity.Bethe.RatioProfile

/-! # Second derivative control for the odd midpoint correction -/

@[expose] public section

open Set
open scoped Topology

namespace PottsDiscontinuity.Bethe

/-- The second derivative of the spectral logarithm off zero. -/
noncomputable def ratioEllSecond (c x : ℝ) : ℝ :=
  1 / (2 * (1 - Real.cos x)) - (c ^ 2 - 1) * Real.cos x / ratioNumerator c x -
    2 * (c ^ 2 - 1) ^ 2 * Real.sin x ^ 2 / ratioNumerator c x ^ 2

theorem ratio_hasDerivAt_ellPrime {c x : ℝ} (hc : 2 < c)
    (hx : x ∈ Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    HasDerivAt (ratioEllPrime c) (ratioEllSecond c x) x := by
  have hn := ratio_numerator_pos hc x
  have hd := ratio_one_sub_cos_pos hx hx0
  have hnum := (Real.hasDerivAt_sin x).const_mul (-(c ^ 2 - 1))
  have hfirst := hnum.div (ratio_hasDerivAt_numerator c x) hn.ne'
  have hlast : HasDerivAt (fun y => Real.sin y / (2 * (1 - Real.cos y)))
      (-1 / (2 * (1 - Real.cos x))) x := by
    apply ((Real.hasDerivAt_sin x).div (ratio_hasDerivAt_two_sub_cos x)
      (mul_pos (by norm_num) hd).ne').congr_deriv
    field_simp [hd.ne']
    nlinarith only [Real.sin_sq_add_cos_sq x]
  apply (hfirst.sub hlast).congr_deriv
  unfold ratioEllSecond
  field_simp [hn.ne', hd.ne'] <;> ring

/-- Removing the quadratic pole gives a uniform bound on the physical interval. -/
theorem ratio_ellSecond_weighted_bound {c : ℝ} (hc : 2 < c) :
    ∃ B ≥ 0, ∀ x ∈ Icc (-Real.pi) Real.pi, |x ^ 2 * ratioEllSecond c x| ≤ B := by
  let R : ℝ → ℝ := fun x => -(c ^ 2 - 1) * Real.cos x / ratioNumerator c x -
    2 * (c ^ 2 - 1) ^ 2 * Real.sin x ^ 2 / ratioNumerator c x ^ 2
  have hA : Continuous (ratioNumerator c) := by unfold ratioNumerator; fun_prop
  have hn (x : ℝ) : ratioNumerator c x ≠ 0 := (ratio_numerator_pos hc x).ne'
  have hR : Continuous R := by unfold R; fun_prop (disch := simp [hn])
  obtain ⟨B₀, hB₀⟩ := (isCompact_Icc : IsCompact (Icc (-Real.pi) Real.pi)).exists_bound_of_continuousOn hR.continuousOn
  let B := max B₀ 0
  refine ⟨Real.pi ^ 2 / 4 + Real.pi ^ 2 * B, by positivity, ?_⟩
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul, abs_zero]
    positivity
  have hd := ratio_one_sub_cos_pos hx hx0
  have hxabs := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  have hx2 : x ^ 2 ≤ Real.pi ^ 2 := by
    simpa using (sq_le_sq₀ (abs_nonneg x) Real.pi_pos.le).mpr hxabs
  have hsing : |x ^ 2 * (1 / (2 * (1 - Real.cos x)))| ≤ Real.pi ^ 2 / 4 := by
    rw [mul_one_div, abs_div, abs_of_nonneg (sq_nonneg x), abs_of_pos (mul_pos (by norm_num) hd)]
    apply (div_le_iff₀ (mul_pos (by norm_num) hd)).mpr
    have hcos := (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mp (ratio_one_sub_cos_lower hx)
    nlinarith only [hcos]
  have hreg : |x ^ 2 * R x| ≤ Real.pi ^ 2 * B := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg x)]
    have hrx0 : |R x| ≤ B₀ := by simpa using hB₀ x hx
    have hrx : |R x| ≤ B := hrx0.trans (le_max_left _ _)
    exact mul_le_mul hx2 hrx (abs_nonneg _) (sq_nonneg _)
  have he : ratioEllSecond c x = 1 / (2 * (1 - Real.cos x)) + R x := by
    unfold ratioEllSecond R
    ring
  rw [he, mul_add]
  exact (abs_add_le _ _).trans (add_le_add hsing hreg)

end PottsDiscontinuity.Bethe
