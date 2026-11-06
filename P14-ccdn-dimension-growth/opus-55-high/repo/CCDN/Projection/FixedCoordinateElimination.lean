/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.IntegerLinearForms
import CCDN.Projection.IntegerHilbertElimination
import CCDN.Projection.ProjectiveClosureProjection
import CCDN.Algebra.ScaledHomogenization
import CCDN.AuxiliaryPolynomial.HypersurfacePositioning

/-!
Full-degree affine elimination also gives an integral projection of the
projective closure, fixing its homogenizing coordinate.

One bounded integer-matrix elimination step on the standard Fin-indexed
polynomial rings, ready for iteration.

The restriction of a bounded homogenization to the hyperplane at infinity
is exactly its highest indicated homogeneous component.
-/

namespace CCDN
open MvPolynomial

/-- For `f` of total degree at most `D`, the degree-`D` homogenization of `f`, restricted to the
hyperplane at infinity `X₀ = 0`, is the degree-`D` homogeneous component of `f`. -/
theorem scaledHomogenize_one_eval_at_infinity {K : Type*} [Field K] {n D : ℕ}
    (f : MvPolynomial (Fin n) K) (hf : f.totalDegree ≤ D) (b : Fin n → K) :
    eval (Fin.cons 0 b) (scaledHomogenize D 1 f) =
      eval b (homogeneousComponent D f) := by
  rw [scaledHomogenize, map_sum, homogeneousComponent_apply, map_sum,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  rw [eval_monomial, homogenizedExponent_value]
  have hle := (le_totalDegree he).trans hf
  by_cases h : e.degree = D
  · have heq : e.sum (fun _ k => k) = D := h
    simp [h, heq, eval_monomial]
  · have hpos : 0 < D - e.sum (fun _ k => k) := by
      change e.sum (fun _ k => k) ≠ D at h
      omega
    simp [h, zero_pow (Nat.ne_of_gt hpos)]

section
variable {n : ℕ} (b : Option (Fin n) → ℤ)

/-- The integer matrix whose `i`-th row is the linear form `b none * X (i + 1) - b (some i) * X 0`,
eliminating the coordinate `X 0` along the direction `b`. -/
def finEliminationMatrix :
    Fin n → Fin (n + 1) → ℤ :=
  fun i => Fin.cases (-b (some i)) (fun j => if j = i then b none else 0)

lemma integerLinearForm_finEliminationMatrix
    (i : Fin n) :
    integerLinearForm (finEliminationMatrix b i) =
      C (b none : ℚ) * X i.succ - C (b (some i) : ℚ) * X 0 := by
  rw [integerLinearForm, linearForm, Fin.sum_univ_succ]
  simp [finEliminationMatrix, apply_ite, ite_mul, sub_eq_add_neg, add_comm]

end

/-- If every entry of the direction `b` lies in `[0, d + 1]`, then every entry of the elimination
matrix has absolute value at most `d + 1`. -/
lemma finEliminationMatrix_height {n d : ℕ} (b : Option (Fin n) → ℤ)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ d + 1) (i : Fin n) (j : Fin (n + 1)) :
    |finEliminationMatrix b i j| ≤ d + 1 := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa [finEliminationMatrix, Fin.cases_zero, abs_neg,
      abs_of_nonneg (hb (some i)).1] using (hb (some i)).2
  · by_cases he : j = i
    · simpa [finEliminationMatrix, Fin.cases_succ, he, ite_true,
        abs_of_nonneg (hb none).1] using (hb none).2
    · simp [finEliminationMatrix, Fin.cases_succ, ite_eq_right he, abs_zero]
      positivity

section
variable (n : ℕ)

/-- The reindexing of `Fin (n + 2)` that sends coordinate `1` to `none` and the remaining
coordinates, in order, to `some 0, some 1, …`; it makes the homogenizing coordinate `0` the first
retained coordinate. -/
def closurePivotEquiv : Fin (n + 2) ≃ Option (Fin (n + 1)) :=
  (Equiv.swap 0 (Fin.succ 0)).trans (finSuccEquiv (n + 1))

/-- The pivot reindexing sends coordinate `0` to `some 0`. -/
@[simp] lemma closurePivotEquiv_zero : closurePivotEquiv n 0 = some 0 := by aesop

/-- The pivot reindexing sends coordinate `1` to `none`. -/
@[simp] lemma closurePivotEquiv_one : closurePivotEquiv n (Fin.succ 0) = none := by aesop

end

/-- The pivot reindexing sends coordinate `i + 2` to `some (i + 1)`. -/
@[simp] lemma closurePivotEquiv_succ_succ {n : ℕ} (i : Fin n) :
    closurePivotEquiv n i.succ.succ = some i.succ := by
  have h0 : i.succ.succ ≠ (0 : Fin (n + 2)) := Fin.succ_ne_zero _
  have h1 : i.succ.succ ≠ (Fin.succ 0 : Fin (n + 2)) := by grind
  simp only [closurePivotEquiv, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne h0 h1]
  rfl

section
variable (n : ℕ)

/-- The inverse pivot reindexing sends `none` to coordinate `1`. -/
@[simp] lemma closurePivotEquiv_symm_none :
    (closurePivotEquiv n).symm none = Fin.succ 0 := by
  exact (closurePivotEquiv n).symm_apply_eq.mpr (closurePivotEquiv_one n).symm

/-- The inverse pivot reindexing sends `some 0` to coordinate `0`. -/
@[simp] lemma closurePivotEquiv_symm_some_zero :
    (closurePivotEquiv n).symm (some 0) = 0 := by
  exact (closurePivotEquiv n).symm_apply_eq.mpr (closurePivotEquiv_zero n).symm

end

/-- The inverse pivot reindexing sends `some (i + 1)` to coordinate `i + 2`. -/
@[simp] lemma closurePivotEquiv_symm_some_succ {n : ℕ} (i : Fin n) :
    (closurePivotEquiv n).symm (some i.succ) = i.succ.succ := by
  exact (closurePivotEquiv n).symm_apply_eq.mpr (closurePivotEquiv_succ_succ i).symm

section
variable {n : ℕ} (b : Option (Fin n) → ℤ)

def closureEliminationDirection :
    Option (Fin (n + 1)) → ℤ :=
  Option.elim' (b none) (Fin.cons 0 (fun i => b (some i)))

lemma closureEliminationDirection_comp :
    (fun i => (closureEliminationDirection b (closurePivotEquiv n i) : ℚ)) =
      Fin.cons 0 (Fin.cons (b none : ℚ) (fun i => (b (some i) : ℚ))) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · aesop
  · refine Fin.cases ?_ (fun j => ?_) j
    · aesop
    · aesop

end

