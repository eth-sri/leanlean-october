/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Projection.ProjectiveClosureProjection
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! Integral projections of the projective closure that fix X₀ specialize
to integral affine projections on the chart X₀ = 1. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- If the projection of the projective closure of `I` by the closure coordinates `X 0, a 0, a 1, …`
is integral, then the affine projection of `I` by the forms `a` is integral. -/
theorem affine_projection_integral_of_closure_integral
    {K : Type*} [Field K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (a : Fin m → MvPolynomial (Fin n) K)
    (hint : (projectionCoordinateMap (projectiveClosureIdeal I)
       (closureProjectionCoordinates a)).IsIntegral) :
    (projectionCoordinateMap I a).IsIntegral := by
  /- Dehomogenization at `X 0 = 1`, as a `K`-algebra homomorphism from polynomials in `n + 1`
  variables to polynomials in `n` variables. -/
  /- Dehomogenizing at `X 0 = 1` an element of the projective closure of `I` gives an element of `I`.
  -/
  /- The specialization `X 0 = 1` from the homogeneous coordinate ring of the projective closure of
  `I` to the affine coordinate ring of `I`. -/
  /- The specialization `X 0 = 1` sends the class of `f` to the class of its dehomogenization. -/
  let chart (k : ℕ) : MvPolynomial (Fin (k + 1)) K →ₐ[K] MvPolynomial (Fin k) K :=
    { toRingHom := affineChart k, commutes' := fun c => by simp [affineChart] }
  let spec : (MvPolynomial (Fin (n + 1)) K ⧸ projectiveClosureIdeal I) →ₐ[K]
      (MvPolynomial (Fin n) K ⧸ I) :=
    Ideal.Quotient.liftₐ (projectiveClosureIdeal I)
      ((Ideal.Quotient.mkₐ K I).comp (chart n)) fun f hf =>
        Ideal.Quotient.eq_zero_iff_mem.mpr <| by
          have h : affineChart n
              (∑ M ∈ Finset.range (f.totalDegree + 1), homogeneousComponent M f) ∈ I := by
            rw [map_sum]
            exact I.sum_mem (fun M _ => (mem_projectiveClosureIdeal_iff I f).mp hf M)
          rwa [sum_homogeneousComponent] at h
  have hspecial : spec.toRingHom.IsIntegral :=
    RingHom.isIntegral_of_surjective _ fun x => by
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨Ideal.Quotient.mk (projectiveClosureIdeal I) (rename Fin.succ f), by
        change Ideal.Quotient.mk I (affineChart n (rename Fin.succ f)) = _
        rw [affineChart_rename_succ]⟩
  have hcomp : (spec.comp (projectionCoordinateMap (projectiveClosureIdeal I)
      (closureProjectionCoordinates a))).IsIntegral :=
    RingHom.IsIntegral.trans
      (projectionCoordinateMap (projectiveClosureIdeal I)
        (closureProjectionCoordinates a)).toRingHom
      spec.toRingHom hint hspecial
  have heq : spec.comp (projectionCoordinateMap (projectiveClosureIdeal I)
      (closureProjectionCoordinates a)) = (projectionCoordinateMap I a).comp (chart m) :=
    AlgHom.ext fun f => by
      change Ideal.Quotient.mk I (affineChart n (aeval (closureProjectionCoordinates a) f)) =
        Ideal.Quotient.mk I (aeval a (affineChart m f))
      rw [affineChart_aeval_closureProjectionCoordinates]
  rw [heq] at hcomp
  exact RingHom.IsIntegral.tower_top (chart m).toRingHom
    (projectionCoordinateMap I a).toRingHom hcomp

end
end CCDN
