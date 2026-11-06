module

public import PottsDiscontinuity.Bethe.RatioProfile

/-! # Second derivative control for the odd midpoint correction -/

@[expose] public section

open Set
open scoped Topology

namespace PottsDiscontinuity.Bethe

section
variable (c x : ℝ)
/-- The second derivative of the spectral logarithm off zero. -/
noncomputable def ratioEllSecond  : ℝ :=
  1 / (2 * (1 - Real.cos x)) - (c ^ 2 - 1) * Real.cos x / ratioNumerator c x -
    2 * (c ^ 2 - 1) ^ 2 * Real.sin x ^ 2 / ratioNumerator c x ^ 2

theorem ratio_hasDerivAt_numerator  :
    HasDerivAt (ratioNumerator c) (-2 * (c ^ 2 - 1) * Real.sin x) x := by
  have hraw := (((Real.hasDerivAt_cos x).const_add 1).const_mul
    (2 * (c ^ 2 - 1))).const_add ((c ^ 2 - 2) ^ 2)
  convert hraw using 1
  · rfl
  simp
end

theorem ratio_hasDerivAt_ellPrime {c x : ℝ} (hc : 2 < c)
    (hx : x ∈ Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    HasDerivAt (ratioEllPrime c) (ratioEllSecond c x) x := by
  have hn := ratio_numerator_pos hc x
  have hd := ratio_one_sub_cos_pos hx hx0
  have hnum := (Real.hasDerivAt_sin x).const_mul (-(c ^ 2 - 1))
  have hfirst := hnum.div (ratio_hasDerivAt_numerator c x) hn.ne'
  have hden : HasDerivAt (fun y => 2 * (1 - Real.cos y)) (2 * Real.sin x) x := by
    convert ((Real.hasDerivAt_cos x).const_sub 1).const_mul 2 using 1
    ring
  have hfirstValue :
      ((-(c ^ 2 - 1) * Real.cos x) * ratioNumerator c x -
        (-(c ^ 2 - 1) * Real.sin x) * (-2 * (c ^ 2 - 1) * Real.sin x)) /
        ratioNumerator c x ^ 2 =
      -(c ^ 2 - 1) * Real.cos x / ratioNumerator c x -
        2 * (c ^ 2 - 1) ^ 2 * Real.sin x ^ 2 / ratioNumerator c x ^ 2 := by
    field_simp
  have hlastValue :
      (Real.cos x * (2 * (1 - Real.cos x)) - Real.sin x * (2 * Real.sin x)) /
        (2 * (1 - Real.cos x)) ^ 2 = -1 / (2 * (1 - Real.cos x)) := by
    field_simp
    nlinarith only [Real.sin_sq_add_cos_sq x]
  have h := hfirst.sub ((Real.hasDerivAt_sin x).div hden (mul_pos (by norm_num) hd).ne')
  apply h.congr_deriv
  rw [hfirstValue, hlastValue]
  unfold ratioEllSecond
  ring

/-- Removing the quadratic pole gives a uniform bound on the physical interval. -/
theorem ratio_ellSecond_weighted_bound {c : ℝ} (hc : 2 < c) :
    ∃ B ≥ 0, ∀ x ∈ Icc (-Real.pi) Real.pi, |x ^ 2 * ratioEllSecond c x| ≤ B := by
  let R := fun x => -(c ^ 2 - 1) * Real.cos x / ratioNumerator c x -
    2 * (c ^ 2 - 1) ^ 2 * Real.sin x ^ 2 / ratioNumerator c x ^ 2
  have hR : Continuous R := by
    have hA : Continuous (ratioNumerator c) := by unfold ratioNumerator; fun_prop
    exact ((continuous_const.mul Real.continuous_cos).div hA
      (fun x => (ratio_numerator_pos hc x).ne')).sub
      ((continuous_const.mul (Real.continuous_sin.pow 2)).div (hA.pow 2)
        (fun x => pow_ne_zero 2 (ratio_numerator_pos hc x).ne'))
  obtain ⟨B₀, hB₀⟩ := (isCompact_Icc : IsCompact (Icc (-Real.pi) Real.pi)).exists_bound_of_continuousOn hR.continuousOn
  let B := max B₀ 0
  have hB : 0 ≤ B := by positivity
  refine ⟨Real.pi ^ 2 / 4 + Real.pi ^ 2 * B, by positivity, ?_⟩
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    simp
    positivity
  have hd := ratio_one_sub_cos_pos hx hx0
  have hxabs : |x| ≤ Real.pi := by grind
  have hx2 : x ^ 2 ≤ Real.pi ^ 2 := by
    simpa using (sq_le_sq₀ (abs_nonneg x) Real.pi_pos.le).mpr hxabs
  have hsing : |x ^ 2 * (1 / (2 * (1 - Real.cos x)))| ≤ Real.pi ^ 2 / 4 := by
    rw [mul_one_div, abs_div, abs_of_nonneg (sq_nonneg x), abs_of_pos (mul_pos (by norm_num) hd)]
    apply (div_le_iff₀ (mul_pos (by norm_num) hd)).mpr
    have hcos := (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mp (ratio_one_sub_cos_lower hx)
    linarith
  have hreg : |x ^ 2 * R x| ≤ Real.pi ^ 2 * B := by
    simp
    have hrx0 : |R x| ≤ B₀ := by simp_all
    have hrx : |R x| ≤ B := by grind
    nlinarith
  have he : ratioEllSecond c x = 1 / (2 * (1 - Real.cos x)) + R x := by
    unfold ratioEllSecond R
    ring
  rw [he, mul_add]
  exact (abs_add_le _ _).trans (add_le_add hsing hreg)

end PottsDiscontinuity.Bethe
