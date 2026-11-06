/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
import CCDN.Algebra.PolynomialMatrixSpecialization

/-! A polynomial matrix with dependent columns at every integer value has a
polynomial kernel vector that remains nonzero at zero. A common power of X is
removed from a kernel vector after its rational denominators are cleared. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Matrix

/-- If every integer specialization has dependent columns, there is a
polynomial relation whose constant coefficient vector is nonzero. -/
theorem polynomial_matrix_kernel_nonzero_at_zero {K ι κ : Type*} [Field K] [CharZero K]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ (Polynomial K))
    (hA : ∀ k : ℕ, ¬ Function.Injective (A.map (Polynomial.evalRingHom (k : K))).mulVecLin) :
    ∃ v : κ → Polynomial K, A *ᵥ v = 0 ∧ ∃ j, (v j).eval 0 ≠ 0 := by
  classical
  have hgen : ¬ Function.Injective
      (A.map (algebraMap (Polynomial K) (RatFunc K))).mulVecLin := fun hi => by
    obtain ⟨k, hk⟩ := polynomial_matrix_injective_specialization A hi
    exact hA k hk
  let f := algebraMap (Polynomial K) (RatFunc K)
  let M := A.map f
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hgen
  let u := x - y
  have hu : u ≠ 0 := sub_ne_zero.mpr hne
  have hMu : M *ᵥ u = 0 := by
    change M.mulVecLin (x - y) = 0
    rw [map_sub, hxy, sub_self]
  obtain ⟨q, C, hq, hC⟩ := ratFunc_matrix_common_denominator (fun i (_ : Unit) => u i)
  let w := fun i => C i ()
  have hw_eq (i : κ) : f (w i) = f q * u i := hC i ()
  have hqf : f q ≠ 0 := RatFunc.algebraMap_ne_zero hq
  have hw : w ≠ 0 := fun hw0 => hu (funext fun i => by
    have hh := hw_eq i
    rw [hw0, Pi.zero_apply, map_zero] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left hqf)
  have hAw : A *ᵥ w = 0 := funext fun i => RatFunc.algebraMap_injective K <| by
    change f (∑ j, A i j * w j) = f 0
    rw [map_sum, map_zero]
    simp only [map_mul, hw_eq]
    rw [show (∑ j, f (A i j) * (f q * u j)) = f q * ∑ j, f (A i j) * u j by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring]
    have hh : ∑ j, f (A i j) * u j = 0 := congrFun hMu i
    rw [hh, mul_zero]
  have hex : ∃ N : ℕ, ∃ i, (w i).coeff N ≠ 0 := by
    by_contra! h
    exact hw (funext fun i => Polynomial.ext fun N => h N i)
  let N := Nat.find hex
  have hdiv (i : κ) : X ^ N ∣ w i :=
    Polynomial.X_pow_dvd_iff.mpr fun m hm => by
      by_contra hn; exact Nat.find_min hex hm ⟨i, hn⟩
  choose v hv using hdiv
  obtain ⟨j0, hj0⟩ := Nat.find_spec hex
  have hv0 : (v j0).eval 0 ≠ 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, ← show (w j0).coeff N = (v j0).coeff 0 by
      rw [hv j0]; simpa only [zero_add] using Polynomial.coeff_X_pow_mul (v j0) N 0]
    exact hj0
  refine ⟨v, funext fun i => ?_, j0, hv0⟩
  apply mul_left_cancel₀ (pow_ne_zero N (Polynomial.X_ne_zero : (X : Polynomial K) ≠ 0))
  simp only [Pi.zero_apply, mul_zero]
  change X ^ N * (∑ j, A i j * v j) = 0
  have hh : ∑ j, A i j * w j = 0 := congrFun hAw i
  rw [Finset.mul_sum, ← hh]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hv j]; ring

end
end CCDN
