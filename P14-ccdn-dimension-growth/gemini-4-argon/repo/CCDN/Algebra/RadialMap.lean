/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Radial scaling `X j ↦ X j * T` of a multivariate polynomial; the coefficient of
`T ^ n` is the homogeneous component of degree `n`. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Replace every coordinate by itself times the same scalar parameter. -/
def radialMap {K σ : Type*} [CommRing K] :
    MvPolynomial σ K →+* Polynomial (MvPolynomial σ K) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun j => Polynomial.C (MvPolynomial.X j) * Polynomial.X)

/- The radial map sends a constant `C c` to the constant polynomial `C (C c)`. -/
/- The radial map sends the variable `X j` to `X j * T`. -/

/-- The coefficient of `T ^ n` in the radial image of `f` is the homogeneous component of
`f` of degree `n`. -/
lemma radialMap_coeff {K σ : Type*} [CommRing K] (f : MvPolynomial σ K) (n : ℕ) :
    (radialMap f).coeff n = homogeneousComponent n f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add, Polynomial.coeff_add, hf, hg]
  | monomial e c =>
    have hm : radialMap (monomial e c) = Polynomial.C (monomial e c) * Polynomial.X ^ e.degree := by
      rw [monomial_eq, map_mul, show radialMap (MvPolynomial.C c : MvPolynomial σ K) =
        Polynomial.C (MvPolynomial.C c) by simp [radialMap], map_finsuppProd]
      simp only [map_pow, show ∀ j : σ, radialMap (MvPolynomial.X j : MvPolynomial σ K) =
        Polynomial.C (MvPolynomial.X j) * Polynomial.X from fun _ => by simp [radialMap], mul_pow]
      rw [Finsupp.prod_mul]
      simp only [← map_pow, Finsupp.prod, ← map_prod, Finset.prod_pow_eq_pow_sum, ← mul_assoc,
        ← Polynomial.C_mul]
      rfl
    rw [hm, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      homogeneousComponent_of_mem (isHomogeneous_monomial c rfl)]
    split_ifs <;> simp_all

end
end CCDN
