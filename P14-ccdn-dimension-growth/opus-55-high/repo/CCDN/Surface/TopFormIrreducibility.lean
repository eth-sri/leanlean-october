/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.RingTheory.MvPolynomial.Homogeneous
import CCDN.Algebra.HomogeneousLinearDescent
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! An irreducible highest homogeneous component forces irreducibility of
 the full polynomial. Coefficient reduction preserves this implication and
 the full degree whenever the reduced highest component remains irreducible. -/

namespace CCDN
section
open MvPolynomial

/-- Applying a ring homomorphism to the coefficients commutes with taking the homogeneous
component of degree `d`. -/
lemma map_homogeneousComponent {R S σ : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (d : ℕ) (f : MvPolynomial σ R) :
    map φ (homogeneousComponent d f) = homogeneousComponent d (map φ f) := by
  ext m
  simp [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

section
variable {K σ : Type*} [Field K] (f : MvPolynomial σ K)

lemma isUnit_of_isUnit_top_homogeneousComponent
    (hu : IsUnit (homogeneousComponent f.totalDegree f)) :
    IsUnit f := by
  have hd : f.totalDegree = 0 := by
    have hhom := (homogeneousComponent_isHomogeneous f.totalDegree f).totalDegree hu.ne_zero
    have hzero := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    omega
  have he := totalDegree_eq_zero_iff_eq_C.mp hd
  rw [hd, homogeneousComponent_zero] at hu
  rwa [he]

/-- The product of highest components detects every proper factorization of
 the full equation, over any field. -/
theorem irreducible_of_top_homogeneousComponent_irreducible
    (hir : Irreducible (homogeneousComponent f.totalDegree f)) : Irreducible f := by
  have hf : f ≠ 0 := by aesop
  refine ⟨?_, ?_⟩
  · intro hu
    have hd := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    have he := totalDegree_eq_zero_iff_eq_C.mp hd
    apply hir.not_isUnit
    rw [hd, homogeneousComponent_zero]
    grind
  · intro g h he
    have hg : g ≠ 0 := by grind
    have hh : h ≠ 0 := by grind
    have hprod : homogeneousComponent f.totalDegree f =
        homogeneousComponent g.totalDegree g * homogeneousComponent h.totalDegree h := by
      rw [he, totalDegree_mul_of_isDomain hg hh, top_homogeneousComponent_mul]
    rcases hir.isUnit_or_isUnit hprod with hu | hu
    · exact Or.inl (isUnit_of_isUnit_top_homogeneousComponent g hu)
    · exact Or.inr (isUnit_of_isUnit_top_homogeneousComponent h hu)

end

/-- If the coefficient image of the original top component is irreducible,
 the full coefficient image has unchanged total degree and is irreducible. -/
theorem map_degree_and_irreducible_of_top_irreducible
    {R K σ : Type*} [CommRing R] [Field K]
    (φ : R →+* K) (f : MvPolynomial σ R)
    (hir : Irreducible (map φ (homogeneousComponent f.totalDegree f))) :
    (map φ f).totalDegree = f.totalDegree ∧ Irreducible (map φ f) := by
  have htop : Irreducible (homogeneousComponent f.totalDegree (map φ f)) := by
    rwa [map_homogeneousComponent] at hir
  have hge : f.totalDegree ≤ (map φ f).totalDegree := by
    by_contra h
    exact htop.ne_zero (homogeneousComponent_eq_zero _ _ (by omega))
  have he := le_antisymm (totalDegree_map_le _ _) hge
  refine ⟨he, ?_⟩
  apply irreducible_of_top_homogeneousComponent_irreducible
  rwa [he]

