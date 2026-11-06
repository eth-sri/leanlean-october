/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Hilbert.LinearProjectionFiltration

/-! Rational-point fibers of an integral polynomial projection.
Evaluation on the quotient constructs the specialization homomorphisms. -/

public section
namespace CCDN
open MvPolynomial

/-- A rational point of the fiber over `z` gives a specialization of the quotient algebra over
the parameter ring, sending each coordinate function to the corresponding coordinate. -/
theorem exists_projection_fiber_specialization {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (l : τ → MvPolynomial σ K)
    [Algebra (MvPolynomial τ K) (MvPolynomial σ K ⧸ I)]
    (hmap : algebraMap (MvPolynomial τ K) (MvPolynomial σ K ⧸ I) =
      (projectionCoordinateMap I l).toRingHom)
    (z : τ → K) (x : σ → K) (hzero : x ∈ idealZeroLocus I)
    (hproj : ∀ i, eval x (l i) = z i) :
    letI : Algebra (MvPolynomial τ K) K := (aeval z).toRingHom.toAlgebra
    ∃ ψ : (MvPolynomial σ K ⧸ I) →ₐ[MvPolynomial τ K] K,
      ∀ i, ψ (Ideal.Quotient.mk I (X i)) = x i := by
  let : Algebra (MvPolynomial τ K) K := (aeval z).toRingHom.toAlgebra
  let R := MvPolynomial τ K
  let A := MvPolynomial σ K ⧸ I
  let φ := Ideal.Quotient.liftₐ I (aeval x) ((hzero))
  have hφ (f : MvPolynomial σ K) :
      φ (Ideal.Quotient.mk I f) = eval x f := rfl
  have hcomp : φ.comp (projectionCoordinateMap I l) = aeval z := by
    aesop (add simp [CCDN.projectionCoordinateMap])
  let ψ : A →ₐ[R] K :=
    { φ.toRingHom with
      commutes' := fun r => by
        change φ (algebraMap R A r) = (aeval z) r
        rw [hmap]
        exact congrArg (fun f : R →ₐ[K] K => f r) hcomp }
  refine ⟨ψ, ?_⟩
  intro i
  change φ (Ideal.Quotient.mk I (X i)) = x i
  simpa only [eval_X] using hφ (X i)

end CCDN
