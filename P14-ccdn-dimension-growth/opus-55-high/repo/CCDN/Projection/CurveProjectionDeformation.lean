/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Hilbert.LinearProjectionFiltration
import CCDN.Plane.LinearDeformation
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import CCDN.Algebra.PolynomialFamilyRelations
import CCDN.Projection.PlaneProjectionDegree
import Mathlib.Algebra.MvPolynomial.Monad

/-! Construct a polynomial family of plane relations for linear
projections of a prime affine curve. The relation has degree at most the
curve's Hilbert degree and remains nonzero at parameter zero. -/

namespace CCDN
section
open MvPolynomial

variable {K τ : Type*} [Field K]

lemma planeLinearDeformation_eval_quotient
    (I : Ideal (MvPolynomial τ K)) (a : Fin 2 → MvPolynomial τ K)
    (l : MvPolynomial τ K) (t : K) (f : MvPolynomial (Fin 2) K) :
    (planeLinearDeformation (fun i => (Ideal.Quotient.mk I) (a i)) 1
      ((Ideal.Quotient.mk I) l) f).eval (algebraMap K (MvPolynomial τ K ⧸ I) t) =
      projectionCoordinateMap I (![a 0, a 1 + t • l]) f := by
  let E : Polynomial (MvPolynomial τ K ⧸ I) →ₐ[K] (MvPolynomial τ K ⧸ I) :=
    (Polynomial.aeval (algebraMap K (MvPolynomial τ K ⧸ I) t)).restrictScalars K
  have he : E.comp (planeLinearDeformation (fun i => (Ideal.Quotient.mk I) (a i)) 1
      ((Ideal.Quotient.mk I) l)) = projectionCoordinateMap I (![a 0, a 1 + t • l]) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [E, planeLinearDeformation, projectionCoordinateMap, Algebra.smul_def]
    change (Ideal.Quotient.mk I) l * algebraMap K (MvPolynomial τ K ⧸ I) t =
      algebraMap K (MvPolynomial τ K ⧸ I) t * (Ideal.Quotient.mk I) l
    ring
  exact congrArg (fun ψ => ψ f) he

