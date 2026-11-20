/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Height.Box
import CCDN.Noether.ShearNormalization
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Coeff

/-! A plane equation of prescribed degree through two rational points. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The equation `X₀ = X₁ ^ d` gives two points and stays irreducible after base change. -/
lemma exists_irreducible_zero_one_equation
    {K L : Type*} [Field K] [Field L] (φ : K →+* L)
    (d : ℕ) (hd : 0 < d) :
    ∃ f : MvPolynomial (Fin 2) K,
      f.totalDegree = d ∧ Irreducible (map φ f) ∧
        eval (0 : Fin 2 → K) f = 0 ∧ eval (fun _ => (1 : K)) f = 0 := by
  classical
  let f : MvPolynomial (Fin 2) K := X 0 - X 1 ^ d
  have hfdeg : f.totalDegree = d := by
    apply le_antisymm
    · simpa [f, max_eq_right (show 1 ≤ d by omega)] using
        totalDegree_sub (X 0 : MvPolynomial (Fin 2) K) (X 1 ^ d)
    · have hc : f.coeff (Finsupp.single 1 d) ≠ 0 := by
        have hne : Finsupp.single (1 : Fin 2) d ≠ Finsupp.single 0 1 := by
          intro h
          simpa using congrArg (fun s : Fin 2 →₀ ℕ => s 0) h
        simp [f, X_pow_eq_monomial, coeff_X, coeff_monomial, hne.symm]
      simpa using le_totalDegree (mem_support_iff.mpr hc)
  have hfir : Irreducible (map φ f) := by
    apply (MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv L)).mp
    simp only [f, map_sub, map_pow, map_X, bivariatePolynomialEquiv_X_zero,
      bivariatePolynomialEquiv_X_one]
    rw [← Polynomial.C_pow]
    exact Polynomial.irreducible_X_sub_C (Polynomial.X ^ d)
  exact ⟨f, hfdeg, hfir, by simp [f, ne_of_gt hd], by simp [f]⟩

end
end CCDN
