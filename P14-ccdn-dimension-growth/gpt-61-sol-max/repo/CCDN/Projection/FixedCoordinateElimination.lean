/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib.Tactic

public import CCDN.Algebra.IntegerLinearForms
public import CCDN.Projection.IntegerHilbertElimination
public import CCDN.Projection.ProjectiveClosureProjection
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

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- For `f` of total degree at most `D`, the degree-`D` homogenization of `f`, restricted to the
hyperplane at infinity `X₀ = 0`, is the degree-`D` homogeneous component of `f`. -/
theorem scaledHomogenize_one_eval_at_infinity {K : Type*} [Field K] {n D : ℕ}
    (f : MvPolynomial (Fin n) K) (hf : f.totalDegree ≤ D) (b : Fin n → K) :
    eval (Fin.cons 0 b) (scaledHomogenize D 1 f) =
      eval b (homogeneousComponent D f) := by
  classical
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

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

variable {n : ℕ} (b : Option (Fin n) → ℤ)

/-- The integer matrix whose `i`-th row is the linear form `b none * X (i + 1) - b (some i) * X 0`,
eliminating the coordinate `X 0` along the direction `b`. -/
def finEliminationMatrix  :
    Fin n → CCDN.IntPoint (n + 1) :=
  fun i => Fin.cases (-b (some i)) (fun j => if j = i then b none else 0)

private lemma integerLinearForm_finEliminationMatrix  (i : Fin n) :
    integerLinearForm (finEliminationMatrix b i) =
      C (b none : ℚ) * X i.succ - C (b (some i) : ℚ) * X 0 := by
  rw [integerLinearForm, linearForm, Fin.sum_univ_succ]
  simp [finEliminationMatrix, apply_ite, ite_mul, sub_eq_add_neg, add_comm]

/-- If every entry of the direction `b` lies in `[0, d + 1]`, then every entry of the elimination
matrix has absolute value at most `d + 1`. -/
lemma finEliminationMatrix_height {n d : ℕ} (b : Option (Fin n) → ℤ)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ d + 1) (i : Fin n) (j : Fin (n + 1)) :
    |finEliminationMatrix b i j| ≤ d + 1 := by
  refine Fin.cases ?_ (fun j => ?_) j
  · grind [CCDN.finEliminationMatrix]
  · grind [finEliminationMatrix, CCDN.finEliminationMatrix]

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- The reindexing of `Fin (n + 2)` that sends coordinate `1` to `none` and the remaining
coordinates, in order, to `some 0, some 1, …`; it makes the homogenizing coordinate `0` the first
retained coordinate. -/
def closurePivotEquiv (n : ℕ)  :=
  (Equiv.swap 0 (Fin.succ 0)).trans (finSuccEquiv (n + 1))


variable {n : ℕ}


/-- The inverse pivot reindexing sends `none` to coordinate `1`. -/
@[simp] lemma closurePivotEquiv_symm_none (n : ℕ) :
    (closurePivotEquiv n).symm none = Fin.succ 0 := by
  rfl

/-- The inverse pivot reindexing sends `some 0` to coordinate `0`. -/
@[simp] lemma closurePivotEquiv_symm_some_zero (n : ℕ) :
    (closurePivotEquiv n).symm (some 0) = 0 := by
  rfl

/-- The inverse pivot reindexing sends `some (i + 1)` to coordinate `i + 2`. -/
@[simp] lemma closurePivotEquiv_symm_some_succ  (i : Fin n) :
    (closurePivotEquiv n).symm (some i.succ) = i.succ.succ := by
  rfl

private def closureEliminationDirection  (b : Option (Fin n) → ℤ)  :=
  Option.elim' (b none) (Fin.cons 0 (fun i => b (some i)))

private lemma closureEliminationDirection_comp  (b : Option (Fin n) → ℤ) :
    (fun i => (closureEliminationDirection b (closurePivotEquiv n i) : ℚ)) =
      Fin.cons 0 (Fin.cons (b none : ℚ) (fun i => (b (some i) : ℚ))) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · rfl


/-- A full-degree direction for an affine ideal equation gives an
integral map of projective closures whose first coordinate remains X₀. -/
theorem fixedCoordinateElimination_isIntegral 
    (I : CCDN.CoordinateIdeal (n + 1))
    (f : CCDN.CoordinatePolynomial (n + 1)) (hf : f ≠ 0) (hfi : f ∈ I)
    (b : Option (Fin n) → ℤ) (hb : (b none : ℚ) ≠ 0)
    (hdir : eval (Fin.cons (b none : ℚ) (fun i => (b (some i) : ℚ)))
      (homogeneousComponent f.totalDegree f) ≠ 0) :
    (projectionCoordinateMap (projectiveClosureIdeal I)
      (closureProjectionCoordinates
        (fun i => integerLinearForm (finEliminationMatrix b i)))).IsIntegral := by
  let H := projectiveClosureIdeal I
  let e := renameEquiv ℚ (closurePivotEquiv n)
  let J := H.map e
  let F := e (scaledHomogenize f.totalDegree 1 f)
  let c := closureEliminationDirection b
  have hc : (c none : ℚ) ≠ 0 := hb
  have hFhom : F.IsHomogeneous f.totalDegree :=
    (scaledHomogenize_homogeneous 1 f le_rfl).rename_isHomogeneous
  have hF0 : F ≠ 0 := by
    intro h
    have hh : scaledHomogenize f.totalDegree 1 f = 0 := e.injective (by
      solve_by_elim [map_zero])
    apply hf
    simpa only [affineChart_scaledHomogenize_one, map_zero] using
      congrArg (affineChart (n + 1)) hh
  have hFdeg := hFhom.totalDegree hF0
  have hFdir : eval (fun i => (c i : ℚ))
      (homogeneousComponent F.totalDegree F) ≠ 0 := by
    rw [hFdeg, homogeneousComponent_eq_self hFhom]
    exact ((show (eval fun i => ↑(closureEliminationDirection b i))
                 ((rename ⇑(closurePivotEquiv n)) (scaledHomogenize (totalDegree f) (1 : ℚ) f)) =
               (eval (Fin.cons ↑(b none) fun i => ↑(b (some i)))) ((homogeneousComponent (totalDegree f)) f) from (by
             rw [eval_rename]
             change eval (fun i => (closureEliminationDirection b (closurePivotEquiv n i) : ℚ))
               (scaledHomogenize f.totalDegree 1 f) = _
             rw [closureEliminationDirection_comp, scaledHomogenize_one_eval_at_infinity f le_rfl]))).trans_ne hdir
  have hFmem : F ∈ J := by
    grind [Ideal.mem_map_of_mem, homogeneous_mem_projectiveClosureIdeal_iff, scaledHomogenize_homogeneous, affineChart_scaledHomogenize_one]
  have hraw : (coordinateEliminationMap J
      (hypersurfaceAffineCoordinates 0 (fun i => (c i : ℚ)) hc)).IsIntegral := by
    apply coordinateEliminationMap_isIntegral J _
      (normalizedHypersurfaceCoordinates 0 (fun i => (c i : ℚ)) hc F)
    · exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hFmem)
    · exact normalizedHypersurfaceCoordinates_monic 0 _ hc F hFdir
  rw [coordinateEliminationMap_eq_projection] at hraw
  have hint := integerEliminationMap_isIntegral J c hc hraw
  have hJ : J = H.map
      (e : CCDN.CoordinatePolynomial (n + 2) →+*
        MvPolynomial (Option (Fin (n + 1))) ℚ) := rfl
  let φ := (Ideal.quotientEquivAlg H J e hJ).symm
  have hφ := RingHom.isIntegral_of_surjective _ φ.surjective
  have hcomp := RingHom.IsIntegral.trans
    (projectionCoordinateMap J (integerEliminationCoordinates c)).toRingHom φ.toRingHom
    hint hφ
  let a := fun i => integerLinearForm (finEliminationMatrix b i)
  let ψ := projectionCoordinateMap H (closureProjectionCoordinates a)
  let χ : CCDN.CoordinatePolynomial (n + 1) →ₐ[ℚ] CCDN.CoordinatePolynomial (n + 1) :=
    aeval (Fin.cons (C (b none : ℚ) * X 0) (fun i => X i.succ))
  have heq : φ.toAlgHom.comp (projectionCoordinateMap J (integerEliminationCoordinates c)) =
      ψ.comp χ := by
    ext i
    simp only [AlgHom.comp_apply, projectionCoordinateMap, aeval_X,
      Ideal.Quotient.mkₐ_eq_mk]
    change φ ((Ideal.Quotient.mk J) (integerEliminationCoordinates c i)) = ψ (χ (X i))
    dsimp only [φ]
    rw [Ideal.quotientEquivAlg_symm, Ideal.quotientEquivAlg_mk]
    refine Fin.cases ?_ (fun j => ?_) i
    · aesop (add simp [integerEliminationCoordinates, closureEliminationDirection, projectionCoordinateMap, closureProjectionCoordinates])
    · simp [integerEliminationCoordinates, c, closureEliminationDirection, e,
        ψ, χ, projectionCoordinateMap, closureProjectionCoordinates, a,
        integerLinearForm_finEliminationMatrix]
  change (φ.toAlgHom.comp
    (projectionCoordinateMap J (integerEliminationCoordinates c))).IsIntegral at hcomp
  rw [heq] at hcomp
  exact RingHom.IsIntegral.tower_top χ.toRingHom ψ.toRingHom hcomp

end
end CCDN
