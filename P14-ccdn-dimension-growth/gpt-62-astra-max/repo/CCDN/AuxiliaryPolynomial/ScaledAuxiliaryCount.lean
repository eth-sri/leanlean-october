/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Algebra.HomogeneousSlice
import CCDN.Algebra.ScaledHomogenizationPrimitive
import CCDN.Algebra.FieldMapIrreducible
import CCDN.Plane.Bezout

/-! Proper affine sections and Bézout counts from prime-scaled homogeneous
models. The coordinate slice is x₀=p, and the original points stay integral. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Let `p` be a prime not dividing the constant coefficient of the primitive integer polynomial
`f`. If a form `g` is not divisible by the `p`-scaled homogenization of `f`, then over `ℚ` its
slice at `x₀ = p` is not divisible by `f`. -/
theorem scaled_auxiliary_rational_not_dvd {n M : ℕ}
    (f : IntegerPolynomial n) (hf0 : f ≠ 0) (hprim : PrimitiveIntegerPolynomial f)
    {p : ℕ} (hp : p.Prime) (hp0 : ¬ (p : ℤ) ∣ f.coeff 0)
    (g : IntegerPolynomial (n + 1)) (hg : g.IsHomogeneous M)
    (hnd : ¬ scaledHomogenize f.totalDegree (p : ℤ) f ∣ g) :
    ¬ rationalEquation f ∣
      rationalEquation (homogeneousSlice n (p : ℤ) g) := by
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hdegree :
      (homogeneousSlice n (p : ℤ) (scaledHomogenize f.totalDegree (p : ℤ) f)).totalDegree =
        f.totalDegree := by
    rw [homogeneousSlice_scaledHomogenize _ _ le_rfl,
      totalDegree_mul_of_isDomain (by aesop) hf0, totalDegree_C,
      zero_add]
  have h := rational_homogeneousSlice_not_dvd hpZ (scaledHomogenize_homogeneous _ _ le_rfl)
    (scaledHomogenize_ne_zero _ hpZ hf0) hg (hprim.scaledHomogenize _ hp hp0) hdegree hnd
  intro hdiv
  apply h
  rw [homogeneousSlice_scaledHomogenize _ _ le_rfl, map_mul, map_C]
  exact_mod_cast ((isUnit_iff_ne_zero.mpr (pow_ne_zero _ hpQ)).map C).mul_left_dvd.mpr hdiv

end
end CCDN
