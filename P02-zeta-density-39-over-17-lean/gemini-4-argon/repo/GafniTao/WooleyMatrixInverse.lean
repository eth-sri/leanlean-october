module
public import GafniTao.WooleyPolynomialNormalForm
public import Mathlib.Algebra.Ring.GeomSum

@[expose] public section

/-!
# The near-identity matrix inversion in Wooley Sections 4 and 7

The coefficient matrices occurring after the polynomial normal-form reduction
are congruent to the identity modulo `p^c`.  Over `ZMod (p^B)` their error is
nilpotent, so the finite geometric series gives an inverse.  This is the exact
algebraic reason that Wooley may replace the transformed congruences by the
monomial congruences; no determinant or assumed inverse is used here.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- A nilpotent element has a finite geometric-series left inverse after
subtracting it from one. -/
theorem wooley_geomSum_mul_one_sub_of_pow_eq_zero
    {R : Type*} [Ring R] (x : R) (m : ℕ) (hx : x ^ m = 0) :
    (∑ i ∈ range m, x ^ i) * (1 - x) = 1 := by
  rw [geom_sum_mul_neg, hx, sub_zero]

/-- Left multiplication by `1-x` is injective when `x` is nilpotent. -/
theorem wooley_one_sub_mul_eq_zero_of_pow_eq_zero
    {R : Type*} [Ring R] (x y : R) (m : ℕ)
    (hx : x ^ m = 0) (hxy : (1 - x) * y = 0) :
    y = 0 := by
  let g : R := ∑ i ∈ range m, x ^ i
  calc
    y = 1 * y := (one_mul y).symm
    _ = (g * (1 - x)) * y := by
      rw [wooley_geomSum_mul_one_sub_of_pow_eq_zero x m hx]
    _ = g * ((1 - x) * y) := by rw [mul_assoc]
    _ = 0 := by rw [hxy, mul_zero]

/-- The scalar `(p^c)` is nilpotent modulo `p^B` as soon as `c` is positive.
The exponent `B+1` handles the degenerate modulus `p^0=1` uniformly. -/
theorem wooley_primePowerScalar_pow_succ_eq_zero
    (p c B : ℕ) (hc : 1 ≤ c) :
    ((p : ZMod (p ^ B)) ^ c) ^ (B + 1) = 0 := by
  rw [← pow_mul]
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  apply pow_dvd_pow p
  exact (Nat.le_succ B).trans
    (Nat.le_mul_of_pos_left (B + 1) (lt_of_lt_of_le Nat.zero_lt_one hc))

/-- The canonical low coefficient matrix, reduced modulo an arbitrary
modulus. -/
def wooleyPolynomialSystemLowMatrixMod {k : ℕ}
    (phi : WooleyPolynomialSystem k) (q : ℕ) :
    Matrix (Fin k) (Fin k) (ZMod q) :=
  fun i j => (wooleyPolynomialSystemLowMatrix phi i j : ZMod q)


