/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import CCDN.Algebra.HomogeneousLinearDescent
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! An irreducible highest homogeneous component forces irreducibility of
 the full polynomial. Coefficient reduction preserves this implication and
 the full degree whenever the reduced highest component remains irreducible. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {R K S σ : Type*} [CommRing R] [Field K] (f : MvPolynomial σ K)

/-- Applying a ring homomorphism to the coefficients commutes with taking the homogeneous
component of degree `d`. -/
lemma map_homogeneousComponent [CommRing S]
    (φ : R →+* S) (d : ℕ) (f : MvPolynomial σ R) :
    map φ (homogeneousComponent d f) = homogeneousComponent d (map φ f) := by
  classical
  ext m
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

private lemma isUnit_of_isUnit_top_homogeneousComponent (hu : IsUnit (homogeneousComponent f.totalDegree f)) :
    IsUnit f := by
  have hd : f.totalDegree = 0 := by
    have hhom := (homogeneousComponent_isHomogeneous f.totalDegree f).totalDegree hu.ne_zero
    have hzero := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    omega
  grind [homogeneousComponent_zero, totalDegree_eq_zero_iff_eq_C.mp]

/-- The product of highest components detects every proper factorization of
 the full equation, over any field. -/
private theorem irreducible_of_top_homogeneousComponent_irreducible
    (hir : Irreducible (homogeneousComponent f.totalDegree f)) : Irreducible f := by
  have hf : f ≠ 0 := by aesop
  refine ⟨?_, ?_⟩
  · intro hu
    have hd := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    grind [totalDegree_eq_zero_iff_eq_C.mp, hir.not_isUnit, homogeneousComponent_zero]
  · intro g h he
    have hg : g ≠ 0 := by grind
    have hh : h ≠ 0 := by grind
    grind [totalDegree_mul_of_isDomain, top_homogeneousComponent_mul, hir.isUnit_or_isUnit, isUnit_of_isUnit_top_homogeneousComponent]

/-- If the coefficient image of the original top component is irreducible,
 the full coefficient image has unchanged total degree and is irreducible. -/
theorem map_degree_and_irreducible_of_top_irreducible
    (φ : R →+* K) (f : MvPolynomial σ R)
    (hir : Irreducible (map φ (homogeneousComponent f.totalDegree f))) :
    (map φ f).totalDegree = f.totalDegree ∧ Irreducible (map φ f) := by
  have htop := by
    rwa [map_homogeneousComponent] at hir
  grind [totalDegree_map_le, htop.ne_zero, homogeneousComponent_eq_zero, le_antisymm, irreducible_of_top_homogeneousComponent_irreducible]

end
end CCDN
