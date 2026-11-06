/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Height.Box
import CCDN.LowerBound.GridMultivariate
import CCDN.Noether.ShearNormalization
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Section 6, Lemma 6.1: an absolutely irreducible rational equation
of prescribed degree vanishes on the entire stated integer box. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- For `d > 0` and `n ≥ 2`, there is a polynomial over `K` in `n` variables of total degree `d`
that stays irreducible over `L` along `φ : K →+* L` and vanishes at both `0` and `(1, …, 1)`. -/
lemma exists_irreducible_zero_one_equation
    {K L : Type*} [Field K] [Field L] (φ : K →+* L)
    (d n : ℕ) (hd : 0 < d) (hn : 2 ≤ n) :
    ∃ f : MvPolynomial (Fin n) K,
      f.totalDegree = d ∧ Irreducible (map φ f) ∧
        eval (0 : Fin n → K) f = 0 ∧ eval (fun _ => (1 : K)) f = 0 := by
  classical
  let f : MvPolynomial (Fin 2) K := X 0 - X 1 ^ d
  have hfdeg : f.totalDegree = d := by
    apply le_antisymm
    · exact (totalDegree_sub _ _).trans (by simp [max_eq_right (show 1 ≤ d by omega)])
    · have he : bivariatePolynomialEquiv K f =
          Polynomial.X - Polynomial.C (Polynomial.X ^ d) := by
        simp [f, bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_X_one]
      have hc : (((bivariatePolynomialEquiv K f).coeff 0).coeff d : K) ≠ 0 := by
        rw [he]
        simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
          Polynomial.coeff_neg, Polynomial.coeff_X_pow, ite_true, zero_sub, neg_ne_zero]
        exact _root_.one_ne_zero
      have hh := bivariateTotalDegree_coeff_le (bivariatePolynomialEquiv K f) 0 d hc
      simpa [bivariateTotalDegree] using hh
  have hfir : Irreducible (map φ f) := by
    apply (MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv L)).mp
    simp only [f, map_sub, map_pow, map_X, bivariatePolynomialEquiv_X_zero,
      bivariatePolynomialEquiv_X_one]
    rw [← Polynomial.C_pow]
    exact Polynomial.irreducible_X_sub_C (Polynomial.X ^ d : Polynomial L)
  let i : Fin 2 → Fin n := Fin.castLE hn
  have hi : Function.Injective i := Fin.castLE_injective hn
  let r : Fin n → Fin 2 := fun j => if j.val = 0 then 0 else 1
  have hr : Function.LeftInverse r i := by
    intro j
    fin_cases j <;> simp [r, i]
  refine ⟨rename i f, ?_, ?_, ?_, ?_⟩
  · rw [totalDegree_rename_of_leftInverse i r hr, hfdeg]
  · rw [map_rename]
    exact irreducible_rename_of_injective i hi _ hfir
  · simp [f, ne_of_gt hd]
  · simp [f]

end
end CCDN
