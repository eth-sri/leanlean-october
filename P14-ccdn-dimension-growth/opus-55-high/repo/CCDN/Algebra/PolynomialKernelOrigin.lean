/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import CCDN.Algebra.PolynomialMatrixSpecialization

/-! A polynomial matrix with dependent columns at every integer value has a
polynomial kernel vector that remains nonzero at zero. A common power of X is
removed from a kernel vector after its rational denominators are cleared. -/

namespace CCDN
section
open Polynomial Matrix

/-- Remove the common order of vanishing of a nonzero polynomial vector. -/
lemma polynomial_vector_remove_common_X {K ι : Type*} [Field K]
    (w : ι → Polynomial K) (hw : w ≠ 0) :
    ∃ N : ℕ, ∃ v : ι → Polynomial K,
      (∀ i, w i = X ^ N * v i) ∧ ∃ i, (v i).eval 0 ≠ 0 := by
  classical
  have hex : ∃ N : ℕ, ∃ i, (w i).coeff N ≠ 0 := by
    by_contra! h
    apply hw
    ext N
    simp_all
  let N := Nat.find hex
  have hdiv (i : ι) : X ^ N ∣ w i := by
    apply Polynomial.X_pow_dvd_iff.mpr
    intro m hm
    by_contra hn
    exact Nat.find_min hex hm ⟨i, hn⟩
  choose v hv using hdiv
  refine ⟨N, v, hv, ?_⟩
  obtain ⟨i, hi⟩ := Nat.find_spec hex
  refine ⟨i, ?_⟩
  have hh : (w i).coeff N = (v i).coeff 0 := by
    rw [hv i]
    simpa using Polynomial.coeff_X_pow_mul (v i) N 0
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  exact hh ▸ hi

/-- Rational-function dependence of columns gives a nonzero polynomial
kernel vector by clearing one common denominator. -/
theorem polynomial_matrix_kernel_of_not_injective {K ι κ : Type*} [Field K]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ (Polynomial K))
    (hA : ¬ Function.Injective (A.map (algebraMap (Polynomial K) (RatFunc K))).mulVecLin) :
    ∃ w : κ → Polynomial K, w ≠ 0 ∧ A *ᵥ w = 0 := by
  let f := algebraMap (Polynomial K) (RatFunc K)
  let M := A.map f
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hA
  let v := x - y
  have hv : v ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨q, C, hq, hC⟩ := ratFunc_matrix_common_denominator
    (fun i (_ : Unit) => v i)
  let w := fun i => C i ()
  have hw (i : κ) : f (w i) = f q * v i := hC i ()
  have hqf : f q ≠ 0 := RatFunc.algebraMap_ne_zero hq
  refine ⟨w, ?_, ?_⟩
  · intro hw0
    apply hv
    funext i
    simp_all
  · funext i
    apply RatFunc.algebraMap_injective K
    change f (∑ j, A i j * w j) = f 0
    rw [map_sum, map_zero]
    simp [map_mul, hw]
    calc
      ∑ j, f (A i j) * (f q * v j) = f q * ∑ j, f (A i j) * v j := by
        rw [Finset.mul_sum]
        grind
      _ = 0 := by
        have hh := congrFun (by
          change M.mulVecLin (x - y) = 0
          grind) i
        change ∑ j, f (A i j) * v j = 0 at hh
        grind

