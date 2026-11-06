/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.HomogeneousSlice
import CCDN.Algebra.ScaledHomogenizationPrimitive
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.Plane.Bezout

/-! Proper affine sections and Bézout counts from prime-scaled homogeneous
models. The coordinate slice is x₀=p, and the original points stay integral. -/

namespace CCDN
section
open MvPolynomial

variable {p : ℕ}

/-- Let `p` be a prime not dividing the constant coefficient of the primitive integer polynomial
`f`. If a form `g` is not divisible by the `p`-scaled homogenization of `f`, then over `ℚ` its
slice at `x₀ = p` is not divisible by `f`. -/
theorem scaled_auxiliary_rational_not_dvd {n M : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf0 : f ≠ 0) (hprim : PrimitiveIntegerPolynomial f)
    (hp : p.Prime) (hp0 : ¬ (p : ℤ) ∣ f.coeff 0)
    (g : MvPolynomial (Fin (n + 1)) ℤ) (hg : g.IsHomogeneous M)
    (hnd : ¬ scaledHomogenize f.totalDegree (p : ℤ) f ∣ g) :
    ¬ MvPolynomial.map (Int.castRingHom ℚ) f ∣
      MvPolynomial.map (Int.castRingHom ℚ) (homogeneousSlice n (p : ℤ) g) := by
  have hpZ : (p : ℤ) ≠ 0 := mod_cast hp.ne_zero
  have hpQ : (p : ℚ) ≠ 0 := mod_cast hp.ne_zero
  have hdegree :
      (homogeneousSlice n (p : ℤ) (scaledHomogenize f.totalDegree (p : ℤ) f)).totalDegree =
        f.totalDegree := by
    rw [homogeneousSlice_scaledHomogenize _ _ le_rfl,
      totalDegree_mul_of_isDomain (C_eq_zero.not.mpr (pow_ne_zero _ hpZ)) hf0, totalDegree_C,
      zero_add]
  have h := rational_homogeneousSlice_not_dvd hpZ (scaledHomogenize_homogeneous _ _ le_rfl)
    (scaledHomogenize_ne_zero _ hpZ hf0) hg (hprim.scaledHomogenize _ hp hp0) hdegree hnd
  intro hdiv
  apply h
  rw [homogeneousSlice_scaledHomogenize _ _ le_rfl, map_mul, map_C]
  simp only [Int.coe_castRingHom, Int.cast_pow]
  have hunit : IsUnit (C (p ^ f.totalDegree) : MvPolynomial (Fin n) ℚ) :=
    (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hpQ)).map C
  exact hunit.mul_left_dvd.mpr hdiv

/-- Once a homogeneous auxiliary nonmultiple has been constructed on the
prime-scaled model, its degree gives the original-plane point bound. -/
theorem scaled_plane_points_card_le_auxiliary_degree {M t : ℕ}
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) f))
    (hp : p.Prime) (hp0 : ¬ (p : ℤ) ∣ f.coeff 0)
    (g : MvPolynomial (Fin 3) ℤ) (hg : g.IsHomogeneous M)
    (hnd : ¬ scaledHomogenize f.totalDegree (p : ℤ) f ∣ g)
    (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z)
    (hz : ∀ i, eval (z i) f = 0)
    (hzg : ∀ i, eval (Fin.cons (p : ℤ) (z i)) g = 0) : t ≤ f.totalDegree * M := by
  exact (integer_common_zeros_card_le _ _ hir (scaled_auxiliary_rational_not_dvd f (fun h => hir.ne_zero (by grind)) hprim hp hp0 g hg hnd) z hinj hz (fun i => by simp_all [homogeneousSlice_eval])).trans (Nat.mul_le_mul_left _ (homogeneousSlice_degree_le _ hg))
