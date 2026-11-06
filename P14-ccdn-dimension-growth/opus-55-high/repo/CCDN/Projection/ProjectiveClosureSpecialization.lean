/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Projection.ProjectiveClosureProjection
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! Integral projections of the projective closure that fix X₀ specialize
to integral affine projections on the chart X₀ = 1. -/

namespace CCDN
noncomputable section
open MvPolynomial

/-- Dehomogenization at `X 0 = 1`, as a `K`-algebra homomorphism from polynomials in `n + 1`
variables to polynomials in `n` variables. -/
def affineChartAlgHom (K : Type*) [Field K] (n : ℕ) :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin n) K where
  toRingHom := affineChart n
  commutes' c := by simp [affineChart]

section
variable {K : Type*} [Field K] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K))

/-- The specialization `X 0 = 1` from the homogeneous coordinate ring of the projective closure of
`I` to the affine coordinate ring of `I`. -/
def projectiveClosureSpecialization
    :
    (MvPolynomial (Fin (n + 1)) K ⧸ projectiveClosureIdeal I) →ₐ[K]
      (MvPolynomial (Fin n) K ⧸ I) :=
  Ideal.Quotient.liftₐ (projectiveClosureIdeal I)
    ((Ideal.Quotient.mkₐ K I).comp (affineChartAlgHom K n))
    (fun f hf => Ideal.Quotient.eq_zero_iff_mem.mpr
      (show affineChart n f ∈ I by
          have h : affineChart n
              (∑ M ∈ Finset.range (f.totalDegree + 1), homogeneousComponent M f) ∈ I := by
            rw [map_sum]
            exact I.sum_mem (fun M _ => (mem_projectiveClosureIdeal_iff I f).mp hf M)
          rwa [sum_homogeneousComponent] at h))

/-- The specialization `X 0 = 1` sends the class of `f` to the class of its dehomogenization. -/
@[simp] lemma projectiveClosureSpecialization_mk
    (f : MvPolynomial (Fin (n + 1)) K) :
    projectiveClosureSpecialization I (Ideal.Quotient.mk (projectiveClosureIdeal I) f) =
      Ideal.Quotient.mk I (affineChart n f) := rfl

end

/-- If the projection of the projective closure of `I` by the closure coordinates `X 0, a 0, a 1, …`
is integral, then the affine projection of `I` by the forms `a` is integral. -/
theorem affine_projection_integral_of_closure_integral
    {K : Type*} [Field K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (a : Fin m → MvPolynomial (Fin n) K)
    (hint : (projectionCoordinateMap (projectiveClosureIdeal I)
      (closureProjectionCoordinates a)).IsIntegral) :
    (projectionCoordinateMap I a).IsIntegral := by
  have hspecial :=
    RingHom.isIntegral_of_surjective _ (show Function.Surjective (projectiveClosureSpecialization I) by
        intro x
        obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
        refine ⟨Ideal.Quotient.mk (projectiveClosureIdeal I) (rename Fin.succ f), ?_⟩
        rw [projectiveClosureSpecialization_mk, affineChart_rename_succ])
  have hcomp := RingHom.IsIntegral.trans
    (projectionCoordinateMap (projectiveClosureIdeal I)
      (closureProjectionCoordinates a)).toRingHom
    (projectiveClosureSpecialization I).toRingHom hint hspecial
  have heq : (projectiveClosureSpecialization I).comp
      (projectionCoordinateMap (projectiveClosureIdeal I) (closureProjectionCoordinates a)) =
        (projectionCoordinateMap I a).comp (affineChartAlgHom K m) := by
    apply AlgHom.ext
    intro f
    change Ideal.Quotient.mk I
      (affineChart n (aeval (closureProjectionCoordinates a) f)) =
        Ideal.Quotient.mk I (aeval a (affineChart m f))
    rw [affineChart_aeval_closureProjectionCoordinates]
  change ((projectiveClosureSpecialization I).comp
      (projectionCoordinateMap (projectiveClosureIdeal I)
        (closureProjectionCoordinates a))).IsIntegral at hcomp
  rw [heq] at hcomp
  exact RingHom.IsIntegral.tower_top (affineChartAlgHom K m).toRingHom
    (projectionCoordinateMap I a).toRingHom hcomp

