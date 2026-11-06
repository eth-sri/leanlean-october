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

/-- Integrality of projective closure projections is stable under composition: if the closure
projection of `I` by homogeneous linear forms `b` is integral, and the closure projection of the
kernel of `b` by `a` is integral, then the closure projection of `I` by the composite forms
`aeval b (a j)` is integral. -/
theorem closure_projection_integral_comp
    {K : Type*} [Field K] {l m n : ℕ}
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
  have hcomp : (φ.comp χ).IsIntegral :=
    RingHom.IsIntegral.trans χ.toRingHom φ.toRingHom haintegral hbintegral.kerLift
  have heq : φ.comp χ = projectionCoordinateMap (projectiveClosureIdeal I)
      (closureProjectionCoordinates (fun j => aeval b (a j))) := by
    ext i
    simp only [AlgHom.comp_apply, χ, projectionCoordinateMap, aeval_X,
      Ideal.Quotient.mkₐ_eq_mk]
    change (Ideal.Quotient.mk (projectiveClosureIdeal I))
      (aeval (closureProjectionCoordinates b) (closureProjectionCoordinates a i)) = _
    congr 1
    refine Fin.cases (by simp [closureProjectionCoordinates]) (fun j => ?_) i
    exact AlgHom.congr_fun
      (by ext k; simp [closureProjectionCoordinates] :
        (aeval (R := K) (closureProjectionCoordinates b)).comp (rename Fin.succ) =
          (rename Fin.succ).comp (aeval b)) (a j)
  rwa [heq] at hcomp

end
end CCDN
