/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousChart

/-! Integral scaled homogenization. The point (h,x) on the homogeneous model
corresponds to the original integer affine point x, without dividing coordinates. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The monomial with exponent `homogenizedExponent d m` evaluated at `(h, x)` equals
`h ^ (d - |m|)` times the monomial `x ^ m`. -/
lemma homogenizedExponent_value
    (d : ℕ) (h : R) (x : Fin n → R) (m : Fin n →₀ ℕ) :
    (homogenizedExponent d m).prod (fun j e => ((Fin.cons h x : Fin (n + 1) → R) j) ^ e) =
      h ^ (d - m.sum (fun _ e => e)) * m.prod (fun j e => x j ^ e) := by
  rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_succ,
    Finsupp.prod_fintype _ _ (by simp)]
  rfl

/-- If `f` has total degree at most `d`, then evaluating `scaledHomogenize d h f` at the point
`(h, x)` gives `h ^ d` times the value of `f` at `x`. -/
theorem scaledHomogenize_eval {d : ℕ}
    (h : R) (f : MvPolynomial (Fin n) R) (hf : f.totalDegree ≤ d) (x : Fin n → R) :
    eval (Fin.cons h x) (scaledHomogenize d h f) = h ^ d * eval x f := by
  classical
  rw [scaledHomogenize, map_sum]
  conv_rhs => rw [f.as_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [eval_monomial, eval_monomial, homogenizedExponent_value]
  grind [← pow_add, Nat.add_sub_of_le ((le_totalDegree hm).trans hf)]

/-- Over a domain, the scaled homogenization of a nonzero polynomial with a nonzero scaling
factor `h` is nonzero. -/
lemma scaledHomogenize_ne_zero [IsDomain R] {n : ℕ}
    (d : ℕ) {h : R} (hh : h ≠ 0) {f : MvPolynomial (Fin n) R} (hf : f ≠ 0) :
    scaledHomogenize d h f ≠ 0 := by
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hf
  intro hz
  have hc := scaledHomogenize_coefficient d h f m
  simp_all

end
end CCDN
