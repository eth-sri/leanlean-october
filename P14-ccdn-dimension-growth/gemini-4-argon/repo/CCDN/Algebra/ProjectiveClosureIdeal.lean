/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousChart
public import CCDN.Algebra.RadialHomogeneousMap
import CCDN.Algebra.PolynomialLinearDescent
import CCDN.Algebra.PolynomialPredicates
import CCDN.Algebra.ProjectiveChartIdeal

/-! The projective closure ideal of an affine coordinate ideal. The
homogenizing parameter is a polynomial variable over the affine quotient,
so primeness and homogeneous components are proved directly. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/- Send the homogenizing coordinate to t and every affine coordinate to
its quotient class times t. -/

/-- The projective closure of the affine coordinate ideal `I`: the homogeneous ideal of
polynomials in `n + 1` variables all of whose homogeneous components dehomogenize (by setting
`X 0 = 1`) into `I`, defined as the kernel of `projectiveClosureMap I`. -/
def projectiveClosureIdeal {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) : Ideal (MvPolynomial (Fin (n + 1)) K) :=
  RingHom.ker ((Polynomial.mapRingHom (Ideal.Quotient.mk I)).comp
    ((Polynomial.mapRingHom (affineChart n)).comp radialMap))

/-- A polynomial lies in the projective closure ideal of `I` if and only if the dehomogenization
of each of its homogeneous components lies in `I`. -/
lemma mem_projectiveClosureIdeal_iff {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (n + 1)) K) :
    f ∈ projectiveClosureIdeal I ↔
      ∀ M, affineChart n (homogeneousComponent M f) ∈ I := by
  /- The coefficient of `t ^ M` in `projectiveClosureMap I f` is the class modulo `I` of the
  dehomogenization of the degree-`M` homogeneous component of `f`. -/
  change (Polynomial.map (Ideal.Quotient.mk I)
    (Polynomial.map (affineChart n) (radialMap f))) = 0 ↔ _
  rw [Polynomial.ext_iff]
  simp only [Polynomial.coeff_map, radialMap_coeff, Polynomial.coeff_zero,
    Ideal.Quotient.eq_zero_iff_mem]

/-- A homogeneous polynomial lies in the projective closure ideal of `I` if and only if its
dehomogenization lies in `I`. -/
lemma homogeneous_mem_projectiveClosureIdeal_iff {K : Type*} [Field K] {n M : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (n + 1)) K)
    (hf : f.IsHomogeneous M) :
    f ∈ projectiveClosureIdeal I ↔ affineChart n f ∈ I := by
  rw [mem_projectiveClosureIdeal_iff]
  constructor
  · intro h
    simpa only [homogeneousComponent_of_mem hf, ite_true] using h M
  · intro h N
    rw [homogeneousComponent_of_mem hf]
    split_ifs <;> simp_all only [map_zero, Ideal.zero_mem]

end
end CCDN
