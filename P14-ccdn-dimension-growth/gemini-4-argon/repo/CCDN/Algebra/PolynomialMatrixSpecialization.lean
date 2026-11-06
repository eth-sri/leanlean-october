/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
import CCDN.Algebra.BoundedLinearSeparation

/-! An injective polynomial matrix over K(t) remains injective at some integer
specialization. Clearing a left inverse's denominators gives the assertion
without selecting minors or assuming a generic-rank principle. -/

@[expose] public section
namespace CCDN
noncomputable section
open Matrix Polynomial

/-- Clear all entries of a rational-function matrix with one nonzero
polynomial denominator. -/
lemma ratFunc_matrix_common_denominator {K ι κ : Type*} [Field K]
    [Fintype ι] [Fintype κ] (B : Matrix ι κ (RatFunc K)) :
    ∃ q : Polynomial K, ∃ C : Matrix ι κ (Polynomial K), q ≠ 0 ∧
      ∀ i j, algebraMap (Polynomial K) (RatFunc K) (C i j) =
        algebraMap (Polynomial K) (RatFunc K) q * B i j := by
  obtain ⟨q, hq⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (Polynomial K)) (fun t : ι × κ => B t.1 t.2)
  choose C hC using hq
  refine ⟨q.val, fun i j => C (i,j), mem_nonZeroDivisors_iff_ne_zero.mp q.property, ?_⟩
  intro i j
  exact (hC (i,j)).trans (Algebra.smul_def _ _)

/-- Full column rank over K(t) occurs at an integer specialization. -/
theorem polynomial_matrix_injective_specialization {K ι κ : Type*} [Field K] [CharZero K]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ (Polynomial K))
    (hA : Function.Injective (A.map (algebraMap (Polynomial K) (RatFunc K))).mulVecLin) :
    ∃ k : ℕ, Function.Injective (A.map (Polynomial.evalRingHom (k : K))).mulVecLin := by
  let f := algebraMap (Polynomial K) (RatFunc K)
  let M := A.map f
  obtain ⟨T, hT⟩ := M.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hA)
  let B := LinearMap.toMatrix' T
  have hBA : B * M = 1 := by
    simpa only [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply',
      LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' hT
  obtain ⟨q, C, hq, hC⟩ := ratFunc_matrix_common_denominator B
  have hCm : C.map f = f q • B := Matrix.ext hC
  have hh : (C * A).map f = f q • (1 : Matrix κ κ (RatFunc K)) := by
    rw [Matrix.map_mul, hCm, Matrix.smul_mul, hBA]
  /- An injective polynomial matrix has a polynomial left inverse up to one
  nonzero scalar polynomial. -/
  have hCA : C * A = q • 1 := Matrix.ext fun i j => RatFunc.algebraMap_injective K <| by
    change f ((C * A) i j) = f ((q • (1 : Matrix κ κ (Polynomial K))) i j)
    simpa only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
      Matrix.one_apply, apply_ite f, map_one, map_zero] using
      congrArg (fun D : Matrix κ κ (RatFunc K) => D i j) hh
  obtain ⟨k, _, hk⟩ := polynomial_exists_small_nat_eval_ne_zero q hq
  refine ⟨k, fun x y hxy => ?_⟩
  let e := Polynomial.evalRingHom (k : K)
  have he : C.map e * A.map e = e q • (1 : Matrix κ κ K) := by
    rw [← Matrix.map_mul, hCA]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
      Matrix.one_apply, apply_ite e, map_one, map_zero]
  have hxy' : (C.map e) *ᵥ ((A.map e) *ᵥ x) = (C.map e) *ᵥ ((A.map e) *ᵥ y) :=
    congrArg ((C.map e) *ᵥ ·) hxy
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, he, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.one_mulVec] at hxy'
  exact smul_right_injective _ hk hxy'

end
end CCDN
