module

public import Mathlib


@[expose] public section

/-!
The quadratic allocation profile in upper_E.  The bounds here are proved
for all admissible real arguments, before asymptotic rounding and summation.
-/

noncomputable section
open scoped BigOperators
open Set

namespace NearlyMinimax

def quadraticProfile (S z : ℝ) : ℝ := S / 4 + (S - z) ^ 2 / S

section
variable {S z : ℝ}

theorem quadraticProfile_lower  (hS : 0 < S) :
    S / 4 ≤ quadraticProfile S z := by
  dsimp [quadraticProfile]
  bound

section
variable (hS : S ≠ 0)
include hS

theorem quadraticProfile_bias_identity   :
    z + quadraticProfile S z - S = (z - S / 2) ^ 2 / S := by
  dsimp [quadraticProfile]
  field_simp
  ring

theorem quadraticProfile_fine_factorization   :
    S ^ 2 / 4 - z * quadraticProfile S z =
      (S - z) * (2 * z - S) ^ 2 / (4 * S) := by
  dsimp [quadraticProfile]
  field_simp
  ring
end


section
variable (hS : 0 < S)
include hS

/-- The sharp maximum used to limit the polynomial-lift variance. -/
theorem quadraticProfile_fine_bound   (hz : z ≤ S) :
    z * quadraticProfile S z ≤ S ^ 2 / 4 := by
  have h := quadraticProfile_fine_factorization (z := z) hS.ne'
  have hn : 0 ≤ (S - z) * (2 * z - S) ^ 2 / (4 * S) := by
    positivity
  linarith

theorem quadraticProfile_fine_upper  
    (hz0 : 0 ≤ z) (hzS : z ≤ S) : quadraticProfile S z ≤ 5 * S / 4 := by
  have hs : (S - z) ^ 2 ≤ S ^ 2 := by
    nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hzS)]
  dsimp [quadraticProfile]
  have hd := (div_le_div_iff_of_pos_right hS).mpr hs
  have he : S ^ 2 / S = S := by field_simp
  
  linarith

theorem quadraticProfile_gaussian_upper   :
    quadraticProfile S z ≤ S + 3 * (z - S / 2) ^ 2 / (2 * S) := by
  have h : S + 3 * (z - S / 2) ^ 2 / (2 * S) - quadraticProfile S z =
      (z + S / 2) ^ 2 / (2 * S) := by
    dsimp [quadraticProfile]
    field_simp
    ring
  have hn : 0 ≤ (z + S / 2) ^ 2 / (2 * S) := by positivity
  linarith
end

end


theorem quadraticProfile_hasDerivAt S z :
    HasDerivAt (quadraticProfile S) (2 * (z - S) / S) z := by
  convert (hasDerivAt_const z (S / 4)).add
    (((hasDerivAt_const z S).sub (hasDerivAt_id z)).pow 2 |>.div_const S) using 1
  · funext x
    simp [quadraticProfile, div_eq_mul_inv]
  · simp only [Pi.sub_apply, id_eq]
    ring

/-- The coarse levels contribute a uniformly bounded factorial series. -/
theorem quadraticProfile_coarse_bound {S z } (hS : 2 ≤ S) (hz : z ≤ 0) :
    Real.exp z * quadraticProfile S z ≤ 5 * S / 4 := by
  
  let f  := fun x => Real.exp x * quadraticProfile S x
  have hd (x : ℝ) : HasDerivAt f
      (Real.exp x * (quadraticProfile S x + 2 * (x - S) / S)) x := by
    convert (Real.hasDerivAt_exp x).mul (quadraticProfile_hasDerivAt S x) using 1
    ring
  have hm : MonotoneOn f (Iic 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iic 0)
      (fun x hx => (hd x).continuousAt.continuousWithinAt)
      (fun x hx => (hd x).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(hd x).deriv]
    have hx0 : x ≤ 0 := by simpa using (interior_subset hx)
    have hprod : 0 ≤ (S - x) * (S - x - 2) := by
      apply mul_nonneg <;> linarith
    have hid : quadraticProfile S x + 2 * (x - S) / S =
        ((S - x) * (S - x - 2) + S ^ 2 / 4) / S := by
      dsimp [quadraticProfile]
      field_simp
      ring
    rw [hid]
    positivity
  have h := hm hz (by simp) hz
  have hzero : f 0 = 5 * S / 4 := by
    dsimp [f, quadraticProfile]
    rw [Real.exp_zero, one_mul]
    field_simp
    ring
  rw [hzero] at h
  exact h

end NearlyMinimax
