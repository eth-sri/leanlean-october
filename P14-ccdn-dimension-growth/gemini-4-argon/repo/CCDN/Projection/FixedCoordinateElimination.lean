/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

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

/-- The integer matrix whose `i`-th row is the linear form `b none * X (i + 1) - b (some i) * X 0`,
eliminating the coordinate `X 0` along the direction `b`. -/
def finEliminationMatrix {n : ℕ} (b : Option (Fin n) → ℤ) :
    Fin n → Fin (n + 1) → ℤ :=
  fun i => Fin.cases (-b (some i)) (fun j => if j = i then b none else 0)

/-- If every entry of the direction `b` lies in `[0, d + 1]`, then every entry of the elimination
matrix has absolute value at most `d + 1`. -/
lemma finEliminationMatrix_height {n d : ℕ} (b : Option (Fin n) → ℤ)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ d + 1) (i : Fin n) (j : Fin (n + 1)) :
    |finEliminationMatrix b i j| ≤ d + 1 := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa only [finEliminationMatrix, Fin.cases_zero, abs_neg,
      abs_of_nonneg (hb (some i)).1] using (hb (some i)).2
  · by_cases he : j = i
    · simpa only [finEliminationMatrix, Fin.cases_succ, he, ite_true,
        abs_of_nonneg (hb none).1] using (hb none).2
    · simp only [finEliminationMatrix, Fin.cases_succ, ite_eq_right he, abs_zero]
      positivity

/-- A full-degree direction for an affine ideal equation gives an
integral map of projective closures whose first coordinate remains X₀. -/
theorem fixedCoordinateElimination_isIntegral {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (f : MvPolynomial (Fin (n + 1)) ℚ) (hf : f ≠ 0) (hfi : f ∈ I)
    (b : Option (Fin n) → ℤ) (hb : (b none : ℚ) ≠ 0)
    (hdir : eval (Fin.cons (b none : ℚ) (fun i => (b (some i) : ℚ)))
      (homogeneousComponent f.totalDegree f) ≠ 0) :
    (projectionCoordinateMap (projectiveClosureIdeal I)
      (closureProjectionCoordinates
        (fun i => integerLinearForm (finEliminationMatrix b i)))).IsIntegral := by
  /- For `f` of total degree at most `D`, the degree-`D` homogenization of `f`, restricted to the
  hyperplane at infinity `X₀ = 0`, is the degree-`D` homogeneous component of `f`. -/
  /- The reindexing of `Fin (n + 2)` that sends coordinate `1` to `none` and the remaining
  coordinates, in order, to `some 0, some 1, …`; it makes the homogenizing coordinate `0` the first
  retained coordinate. -/
  /- The pivot reindexing sends coordinate `0` to `some 0`. -/
  /- The pivot reindexing sends coordinate `1` to `none`. -/
  /- The pivot reindexing sends coordinate `i + 2` to `some (i + 1)`. -/
  /- The inverse pivot reindexing sends `none` to coordinate `1`. -/
  /- The inverse pivot reindexing sends `some 0` to coordinate `0`. -/
  /- The inverse pivot reindexing sends `some (i + 1)` to coordinate `i + 2`. -/
  classical
  let pivot : Fin (n + 2) ≃ Option (Fin (n + 1)) :=
    (Equiv.swap 0 (Fin.succ 0)).trans (finSuccEquiv (n + 1))
  have hp0 : pivot 0 = some 0 := by simp [pivot]
  have hp1 : pivot (Fin.succ 0) = none := by simp [pivot]
  have hpss (i : Fin n) : pivot i.succ.succ = some i.succ := by
    have h0 : i.succ.succ ≠ (0 : Fin (n + 2)) := Fin.succ_ne_zero _
    have h1 : i.succ.succ ≠ (Fin.succ 0 : Fin (n + 2)) := fun h =>
      Fin.succ_ne_zero i (Fin.succ_injective _ h)
    simp only [pivot, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne h0 h1]
    rfl
  have hps_none : pivot.symm none = Fin.succ 0 := pivot.symm_apply_eq.mpr hp1.symm
  have hps_zero : pivot.symm (some 0) = 0 := pivot.symm_apply_eq.mpr hp0.symm
  have hps_succ (i : Fin n) : pivot.symm (some i.succ) = i.succ.succ :=
    pivot.symm_apply_eq.mpr (hpss i).symm
  let H := projectiveClosureIdeal I
  let e := renameEquiv ℚ pivot
  let J := H.map e
  let F := e (scaledHomogenize f.totalDegree 1 f)
  let c : Option (Fin (n + 1)) → ℤ := Option.elim' (b none) (Fin.cons 0 fun i => b (some i))
  have hc : (c none : ℚ) ≠ 0 := hb
  have hFhom : F.IsHomogeneous f.totalDegree :=
    (scaledHomogenize_homogeneous 1 f le_rfl).rename_isHomogeneous
  have hF0 : F ≠ 0 := fun h => hf (by
    have hh : scaledHomogenize f.totalDegree 1 f = 0 := e.injective
      (by change e (scaledHomogenize f.totalDegree 1 f) = e 0; rw [map_zero]; exact h)
    simpa only [affineChart_scaledHomogenize_one, map_zero] using
      congrArg (affineChart (n + 1)) hh)
  have hFdir : eval (fun i => (c i : ℚ)) (homogeneousComponent F.totalDegree F) ≠ 0 := by
    rw [hFhom.totalDegree hF0, homogeneousComponent_eq_self hFhom]
    change eval _ (rename pivot (scaledHomogenize f.totalDegree 1 f)) ≠ 0
    rw [eval_rename, show (fun i => (c i : ℚ)) ∘ pivot =
        Fin.cons 0 (Fin.cons (b none : ℚ) fun i => (b (some i) : ℚ)) by
      funext i
      refine Fin.cases (by simp [c, hp0]) (fun j => Fin.cases
        (by rw [Function.comp_apply, hp1]; rfl)
        (fun j => by rw [Function.comp_apply, hpss]; rfl) j) i]
    have hinf : eval (Fin.cons 0 (Fin.cons (b none : ℚ) fun i => (b (some i) : ℚ)))
        (scaledHomogenize f.totalDegree 1 f) =
        eval (Fin.cons (b none : ℚ) fun i => (b (some i) : ℚ))
          (homogeneousComponent f.totalDegree f) := by
      rw [scaledHomogenize, map_sum, homogeneousComponent_apply, map_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [eval_monomial, homogenizedExponent_value]
      have hle : m.sum (fun _ k => k) ≤ f.totalDegree := le_totalDegree hm
      by_cases h : m.degree = f.totalDegree
      · have heq : m.sum (fun _ k => k) = f.totalDegree := h
        simp [h, heq, eval_monomial]
      · have hpos : 0 < f.totalDegree - m.sum (fun _ k => k) := by
          change m.sum (fun _ k => k) ≠ f.totalDegree at h; omega
        simp [h, zero_pow (Nat.ne_of_gt hpos)]
    rwa [hinf]
  have hFmem : F ∈ J := by
    apply Ideal.mem_map_of_mem
    rwa [homogeneous_mem_projectiveClosureIdeal_iff I _
      (scaledHomogenize_homogeneous 1 f le_rfl), affineChart_scaledHomogenize_one]
  have hraw : (coordinateEliminationMap J
      (hypersurfaceAffineCoordinates 0 (fun i => (c i : ℚ)) hc)).IsIntegral :=
    coordinateEliminationMap_isIntegral J _
      (normalizedHypersurfaceCoordinates 0 (fun i => (c i : ℚ)) hc F)
      (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hFmem))
      (normalizedHypersurfaceCoordinates_monic 0 _ hc F hFdir)
  rw [coordinateEliminationMap_eq_projection] at hraw
  have hJ : J = H.map (e : MvPolynomial (Fin (n + 2)) ℚ →+*
      MvPolynomial (Option (Fin (n + 1))) ℚ) := rfl
  let φ := (Ideal.quotientEquivAlg H J e hJ).symm
  have hcomp := RingHom.IsIntegral.trans
    (projectionCoordinateMap J (integerEliminationCoordinates c)).toRingHom φ.toRingHom
    (integerEliminationMap_isIntegral J c hc hraw)
    (RingHom.isIntegral_of_surjective _ φ.surjective)
  let a := fun i => integerLinearForm (finEliminationMatrix b i)
  let ψ := projectionCoordinateMap H (closureProjectionCoordinates a)
  let χ : MvPolynomial (Fin (n + 1)) ℚ →ₐ[ℚ] MvPolynomial (Fin (n + 1)) ℚ :=
    aeval (Fin.cons (C (b none : ℚ) * X 0) fun i => X i.succ)
  have heq : φ.toAlgHom.comp (projectionCoordinateMap J (integerEliminationCoordinates c)) =
      ψ.comp χ := by
    ext i
    simp only [AlgHom.comp_apply, projectionCoordinateMap, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    change φ ((Ideal.Quotient.mk J) (integerEliminationCoordinates c i)) = ψ (χ (X i))
    dsimp only [φ]
    rw [Ideal.quotientEquivAlg_symm, Ideal.quotientEquivAlg_mk]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [integerEliminationCoordinates, c, e, ψ, χ, projectionCoordinateMap,
        closureProjectionCoordinates, hps_zero]
    · have hlin : integerLinearForm (finEliminationMatrix b j) =
          C (b none : ℚ) * X j.succ - C (b (some j) : ℚ) * X 0 := by
        rw [integerLinearForm, linearForm, Fin.sum_univ_succ]
        simp [finEliminationMatrix, apply_ite, ite_mul, sub_eq_add_neg, add_comm]
      simp [integerEliminationCoordinates, c, e, ψ, χ, projectionCoordinateMap,
        closureProjectionCoordinates, a, hlin, hps_none, hps_succ]
  change (φ.toAlgHom.comp
    (projectionCoordinateMap J (integerEliminationCoordinates c))).IsIntegral at hcomp
  rw [heq] at hcomp
  exact RingHom.IsIntegral.tower_top χ.toRingHom ψ.toRingHom hcomp

end
end CCDN
