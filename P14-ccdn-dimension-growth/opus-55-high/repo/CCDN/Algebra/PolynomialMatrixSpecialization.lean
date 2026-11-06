/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import CCDN.Algebra.BoundedLinearSeparation

/-! An injective polynomial matrix over K(t) remains injective at some integer
specialization. Clearing a left inverse's denominators gives the assertion
without selecting minors or assuming a generic-rank principle. -/

namespace CCDN
section
open Matrix Polynomial

variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]

/-- Clear all entries of a rational-function matrix with one nonzero
polynomial denominator. -/
lemma ratFunc_matrix_common_denominator
    (B : Matrix ι κ (RatFunc K)) :
    ∃ q : Polynomial K, ∃ C : Matrix ι κ (Polynomial K), q ≠ 0 ∧
      ∀ i j, algebraMap (Polynomial K) (RatFunc K) (C i j) =
        algebraMap (Polynomial K) (RatFunc K) q * B i j := by
  obtain ⟨q, hq⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (Polynomial K)) (fun t : ι × κ => B t.1 t.2)
  choose C hC using hq
  refine ⟨q.val, fun i j => C (i,j), mem_nonZeroDivisors_iff_ne_zero.mp q.property, ?_⟩
  intro i j
  exact (hC (i,j)).trans (Algebra.smul_def _ _)

/-- An injective polynomial matrix has a polynomial left inverse up to one
nonzero scalar polynomial. -/
theorem polynomial_matrix_scaled_left_inverse
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ (Polynomial K))
    (hA : Function.Injective (A.map (algebraMap (Polynomial K) (RatFunc K))).mulVecLin) :
    ∃ q : Polynomial K, ∃ C : Matrix κ ι (Polynomial K), q ≠ 0 ∧ C * A = q • 1 := by
  let f := algebraMap (Polynomial K) (RatFunc K)
  let M := A.map f
  obtain ⟨T, hT⟩ := M.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hA)
  let B := LinearMap.toMatrix' T
  have hBA : B * M = 1 := by
    have hh := congrArg LinearMap.toMatrix' hT
    simpa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply',
      LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] using hh
  obtain ⟨q, C, hq, hC⟩ := ratFunc_matrix_common_denominator B
  refine ⟨q, C, hq, ?_⟩
  have hCm : C.map f = f q • B := by ext i j; exact hC i j
  have hh : (C * A).map f = f q • (1 : Matrix κ κ (RatFunc K)) := by aesop
  apply Matrix.ext
  intro i j
  apply RatFunc.algebraMap_injective K
  change f ((C * A) i j) = f ((q • (1 : Matrix κ κ (Polynomial K))) i j)
  have he := congrArg (fun D => D i j) hh
  simpa [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
    Matrix.one_apply, apply_ite f, map_one, map_zero] using he

