/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.ProjectiveClosureIdeal
import CCDN.Hilbert.LinearProjectionFiltration
import CCDN.Algebra.ProjectionScalarExtension
import CCDN.Projection.HomogeneousFilteredProjection

/-! Homogenizing a linear affine projection while retaining its homogenizing
coordinate gives the projective closure of its affine image ideal. -/

namespace CCDN
noncomputable section
open MvPolynomial

section
variable {K : Type*} [Field K] {m n : ℕ} (a : Fin m → MvPolynomial (Fin n) K)

/-- The homogenization of a projection by forms `a`: the forms `X 0, a 0, a 1, …` on the projective
coordinates, which keep the homogenizing coordinate `X 0` and shift the variables of each `a i`. -/
def closureProjectionCoordinates
    :
    Fin (m + 1) → MvPolynomial (Fin (n + 1)) K :=
  Fin.cons (X 0) (fun i => rename Fin.succ (a i))

end

variable {K : Type*} [Field K]

/-- Dehomogenizing at `X 0 = 1` a polynomial not involving `X 0` recovers the original polynomial.
-/
lemma affineChart_rename_succ {n : ℕ}
    (f : MvPolynomial (Fin n) K) :
    affineChart n (rename Fin.succ f) = f := by
  have h : (affineChart (K := K) n).comp
      (rename (R := K) Fin.succ).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [affineChart]
    · intro i
      simp [affineChart]
  exact RingHom.congr_fun h f

/-- Dehomogenization at `X 0 = 1` intertwines substitution of the closure projection coordinates
with substitution of the original forms `a`. -/
lemma affineChart_aeval_closureProjectionCoordinates
    {m n : ℕ}
    (a : Fin m → MvPolynomial (Fin n) K)
    (f : MvPolynomial (Fin (m + 1)) K) :
    affineChart n (aeval (closureProjectionCoordinates a) f) =
      aeval a (affineChart m f) := by
  have h : (affineChart (K := K) n).comp (aeval (closureProjectionCoordinates a)).toRingHom =
      (aeval (R := K) a).toRingHom.comp (affineChart (K := K) m) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [affineChart]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [closureProjectionCoordinates, affineChart]
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          aeval_X, closureProjectionCoordinates, Fin.cons_succ,
          affineChart_rename_succ]
        simp [affineChart]
  exact RingHom.congr_fun h f

