/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.HomogeneousChart
import CCDN.Algebra.RadialHomogeneousMap
import CCDN.Algebra.IdealScalarDescent
import CCDN.Algebra.ProjectiveChartScalarExtension
import CCDN.Hilbert.HomogeneousPrimeComponents

/-! The projective closure ideal of an affine coordinate ideal. The
homogenizing parameter is a polynomial variable over the affine quotient,
so primeness and homogeneous components are proved directly. -/

namespace CCDN
noncomputable section
open MvPolynomial

section
variable {K : Type*} [Field K] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K))

/-- Send the homogenizing coordinate to t and every affine coordinate to
its quotient class times t. -/
def projectiveClosureMap
    :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] Polynomial (MvPolynomial (Fin n) K ⧸ I) where
  toRingHom := (Polynomial.mapRingHom (Ideal.Quotient.mk I)).comp
    ((Polynomial.mapRingHom (affineChart n)).comp radialMap)
  commutes' c := by
    change Polynomial.map (Ideal.Quotient.mk I)
      (Polynomial.map (affineChart n) (radialMap (MvPolynomial.C c))) = _
    simp only [radialMap_C, Polynomial.map_C]
    rw [show affineChart n (C c) = C c by simp [affineChart], Polynomial.algebraMap_apply]
    congr 1

/-- The coefficient of `t ^ M` in `projectiveClosureMap I f` is the class modulo `I` of the
dehomogenization of the degree-`M` homogeneous component of `f`. -/
lemma projectiveClosureMap_coeff
    (f : MvPolynomial (Fin (n + 1)) K) (M : ℕ) :
    (projectiveClosureMap I f).coeff M =
      Ideal.Quotient.mk I (affineChart n (homogeneousComponent M f)) := by
  change ((Polynomial.map (Ideal.Quotient.mk I))
    (Polynomial.map (affineChart n) (radialMap f))).coeff M = _
  simp [Polynomial.coeff_map, radialMap_coeff]

/-- The projective closure of the affine coordinate ideal `I`: the homogeneous ideal of
polynomials in `n + 1` variables all of whose homogeneous components dehomogenize (by setting
`X 0 = 1`) into `I`, defined as the kernel of `projectiveClosureMap I`. -/
def projectiveClosureIdeal
    : Ideal (MvPolynomial (Fin (n + 1)) K) :=
  RingHom.ker (projectiveClosureMap I)

end

variable {K : Type*} [Field K]

/-- A polynomial lies in the projective closure ideal of `I` if and only if the dehomogenization
of each of its homogeneous components lies in `I`. -/
lemma mem_projectiveClosureIdeal_iff {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (n + 1)) K) :
    f ∈ projectiveClosureIdeal I ↔
      ∀ M, affineChart n (homogeneousComponent M f) ∈ I := by
  change projectiveClosureMap I f = 0 ↔ _
  rw [Polynomial.ext_iff]
  simp [projectiveClosureMap_coeff, Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem]

/-- A homogeneous polynomial lies in the projective closure ideal of `I` if and only if its
dehomogenization lies in `I`. -/
lemma homogeneous_mem_projectiveClosureIdeal_iff {n M : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (n + 1)) K)
    (hf : f.IsHomogeneous M) :
    f ∈ projectiveClosureIdeal I ↔ affineChart n f ∈ I := by
  rw [mem_projectiveClosureIdeal_iff]
  constructor
  · intro h
    simpa [homogeneousComponent_of_mem hf, ite_true] using h M
  · intro h N
    rw [homogeneousComponent_of_mem hf]
    split_ifs <;> simp_all

