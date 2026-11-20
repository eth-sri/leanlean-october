/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Projection.ProjectiveClosureProjection
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! Closure-preserving integral affine projections compose. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {K : Type*} [Field K] {l m n : ℕ}

private lemma aeval_closureProjectionCoordinates_rename
    (a : Fin m → MvPolynomial (Fin n) K) (f : MvPolynomial (Fin m) K) :
    aeval (closureProjectionCoordinates a) (rename Fin.succ f) =
      rename Fin.succ (aeval a f) := by
  have h : (aeval (R := K) (closureProjectionCoordinates a)).comp (rename Fin.succ) =
      (rename Fin.succ).comp (aeval a) := by
    aesop
  exact AlgHom.congr_fun h f

private lemma closureProjectionCoordinates_comp
    (a : Fin l → MvPolynomial (Fin m) K)
    (b : Fin m → MvPolynomial (Fin n) K) (i : Fin (l + 1)) :
    aeval (closureProjectionCoordinates b) (closureProjectionCoordinates a i) =
      closureProjectionCoordinates (fun j => aeval b (a j)) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [closureProjectionCoordinates]
  solve_by_elim [aeval_closureProjectionCoordinates_rename]

/-- Integrality of projective closure projections is stable under composition: if the closure
projection of `I` by homogeneous linear forms `b` is integral, and the closure projection of the
kernel of `b` by `a` is integral, then the closure projection of `I` by the composite forms
`aeval b (a j)` is integral. -/
theorem closure_projection_integral_comp
    (I : Ideal (MvPolynomial (Fin n) K))
    (b : Fin m → MvPolynomial (Fin n) K) (hb : ∀ i, (b i).IsHomogeneous 1)
    (a : Fin l → MvPolynomial (Fin m) K)
    (hbintegral : (projectionCoordinateMap (projectiveClosureIdeal I)
      (closureProjectionCoordinates b)).IsIntegral)
    (haintegral : (projectionCoordinateMap
      (projectiveClosureIdeal (RingHom.ker (projectionCoordinateMap I b)))
      (closureProjectionCoordinates a)).IsIntegral) :
    (projectionCoordinateMap (projectiveClosureIdeal I)
      (closureProjectionCoordinates (fun j => aeval b (a j)))).IsIntegral := by
  rw [projectiveClosureIdeal_projection_kernel I b hb] at haintegral
  let ψ := projectionCoordinateMap (projectiveClosureIdeal I) (closureProjectionCoordinates b)
  let φ := Ideal.kerLiftAlg ψ
  let χ := projectionCoordinateMap (RingHom.ker ψ) (closureProjectionCoordinates a)
  have hcomp := RingHom.IsIntegral.trans χ.toRingHom φ.toRingHom haintegral hbintegral.kerLift
  have heq : φ.comp χ = projectionCoordinateMap _
      (closureProjectionCoordinates (fun j => aeval b (a j))) := by
    ext i
    simp only [AlgHom.comp_apply, χ, projectionCoordinateMap, aeval_X,
      Ideal.Quotient.mkₐ_eq_mk]
    change (Ideal.Quotient.mk _)
      (aeval _ (closureProjectionCoordinates a i)) = _
    rw [closureProjectionCoordinates_comp]
  change (φ.comp χ).IsIntegral at hcomp
  aesop

end
end CCDN
