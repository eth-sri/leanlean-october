/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.FieldSimp

/-! Explicit absolutely irreducible equations through a Cartesian grid.
The construction uses Eisenstein at the inner coordinate zero. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

/-- The inner correction has prescribed degree and makes the first coefficient
of the constant outer coefficient nonzero. -/
def gridEisensteinCorrection {K : Type*} [Field K] (V : K[X]) (k : ℕ) : K[X] :=
  V * (X ^ k + C (V.coeff 1 / V.coeff 0 + 1) * X)

/-- The outer variable is the first coordinate, the inner variable the second.
At roots of V in both coordinates all three summands vanish. -/
def gridEisensteinPolynomial {K : Type*} [Field K] (V : K[X]) (k : ℕ) : K[X][X] :=
  V.map C + C (V * C (V.coeff 0)⁻¹) * (X ^ V.natDegree - V.map C) +
    C (gridEisensteinCorrection V k)

/-- The `i`-th coefficient of `gridEisensteinPolynomial V k` in the outer variable, written out from
its three summands. -/
lemma gridEisensteinPolynomial_coeff {K : Type*} [Field K]
    (V : K[X]) (k i : ℕ) :
    (gridEisensteinPolynomial V k).coeff i =
      C (V.coeff i) + V * C (V.coeff 0)⁻¹ *
        ((X ^ V.natDegree : K[X][X]).coeff i - C (V.coeff i)) +
      if i = 0 then gridEisensteinCorrection V k else 0 := by
  simp only [gridEisensteinPolynomial, coeff_add, coeff_map, coeff_C_mul, coeff_sub, coeff_C]

/-- Absolute irreducibility of the explicit construction, over every field. -/
theorem gridEisensteinPolynomial_irreducible {K : Type*} [Field K]
    (V : K[X]) (k : ℕ) (hm : V.Monic) (hd : 0 < V.natDegree)
    (h0 : V.coeff 0 ≠ 0) (hk : 2 ≤ k) :
    Irreducible (gridEisensteinPolynomial V k) := by
  let f := gridEisensteinPolynomial V k
  have hle : f.natDegree ≤ V.natDegree :=
    natDegree_le_iff_coeff_eq_zero.mpr fun i hi => by
      rw [gridEisensteinPolynomial_coeff, ite_eq_right (by omega : i ≠ 0)]
      simp [coeff_eq_zero_of_natDegree_lt hi, coeff_X_pow, ne_of_gt hi]
  have htop : f.coeff V.natDegree = 1 := by
    rw [gridEisensteinPolynomial_coeff, hm.coeff_natDegree]; simp [ne_of_gt hd]
  have hmon : f.Monic := monic_of_natDegree_le_of_coeff_eq_one V.natDegree hle htop
  have hdeg : f.natDegree = V.natDegree :=
    le_antisymm hle (le_natDegree_of_ne_zero (htop ▸ one_ne_zero))
  have he : (evalRingHom (0 : K)).comp C = RingHom.id K := by ext a; simp
  have hred : f.map (evalRingHom 0) = X ^ V.natDegree := by
    simp only [f, gridEisensteinPolynomial, gridEisensteinCorrection, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X, map_map, he, map_id]
    simp [← coeff_zero_eq_eval_zero, h0, show k ≠ 0 by omega]
  have hsimple : (f.coeff 0).coeff 1 = V.coeff 0 := by
    have hc : f.coeff 0 = C (V.coeff 0) - V + gridEisensteinCorrection V k := by
      rw [gridEisensteinPolynomial_coeff]
      simp only [coeff_X_pow, ne_of_lt hd, ite_false, zero_sub, ite_true]
      rw [mul_neg, mul_assoc, ← C_mul, inv_mul_cancel₀ h0, C_1, mul_one]; rfl
    rw [hc]
    simp only [gridEisensteinCorrection, mul_add, coeff_add, coeff_sub, coeff_C,
      one_ne_zero, ite_false, zero_sub]
    rw [coeff_mul_X_pow', ite_eq_right (by omega : ¬ k ≤ 1), ← mul_assoc, coeff_mul_X, coeff_mul_C]
    field_simp; ring
  let P : Ideal K[X] := Ideal.span {X}
  have hp : P.IsPrime := Ideal.isPrime_span_singleton_of_prime prime_X
  apply Polynomial.IsEisensteinAt.irreducible (𝓟 := P) _ hp hmon.isPrimitive (hdeg ▸ hd)
  refine ⟨hmon.leadingCoeff_notMem hp.ne_top, ?_, ?_⟩
  · intro i hi
    rw [Ideal.mem_span_singleton, X_dvd_iff]
    have hcoeff := congrArg (fun q : K[X] => q.coeff i) hred
    simpa [coeff_map, coeff_X_pow, ne_of_lt (hdeg ▸ hi), ← coeff_zero_eq_eval_zero] using hcoeff
  · intro h
    change f.coeff 0 ∈ (Ideal.span ({X} : Set K[X])) ^ 2 at h
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    exact h0 (hsimple ▸ (X_pow_dvd_iff.mp h) 1 (by decide))

/-- `gridEisensteinPolynomial V k` vanishes at every point `(x, y)` whose coordinates are both roots
of `V`. -/
lemma gridEisensteinPolynomial_eval_zero {K : Type*} [Field K]
    (V : K[X]) (k : ℕ) (x y : K) (hx : V.eval x = 0) (hy : V.eval y = 0) :
    ((gridEisensteinPolynomial V k).map (evalRingHom y)).eval x = 0 := by
  have he : (evalRingHom y).comp C = RingHom.id K := by ext a; simp
  simp [gridEisensteinPolynomial, gridEisensteinCorrection, map_map, he, hx, hy]

end
end CCDN
