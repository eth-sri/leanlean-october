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

/-- Applying a ring homomorphism to the coefficients commutes with taking the homogeneous
component of degree `d`. -/
lemma map_homogeneousComponent {R S σ : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (d : ℕ) (f : MvPolynomial σ R) :
    map φ (homogeneousComponent d f) = homogeneousComponent d (map φ f) := by
  classical
  ext m
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

/-- If the coefficient image of the original top component is irreducible,
 the full coefficient image has unchanged total degree and is irreducible. -/
theorem map_degree_and_irreducible_of_top_irreducible
    {R K σ : Type*} [CommRing R] [Field K]
    (φ : R →+* K) (f : MvPolynomial σ R)
    (hir : Irreducible (map φ (homogeneousComponent f.totalDegree f))) :
    (map φ f).totalDegree = f.totalDegree ∧ Irreducible (map φ f) := by
  have hunit (p : MvPolynomial σ K) (hu : IsUnit (homogeneousComponent p.totalDegree p)) :
      IsUnit p := by
    have hd : p.totalDegree = 0 := by
      have hhom := (homogeneousComponent_isHomogeneous p.totalDegree p).totalDegree hu.ne_zero
      have hzero := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
      omega
    have he := totalDegree_eq_zero_iff_eq_C.mp hd
    rw [hd, homogeneousComponent_zero] at hu
    rwa [he]
  have htop : Irreducible (homogeneousComponent f.totalDegree (map φ f)) := by
    rwa [map_homogeneousComponent] at hir
  have hge : f.totalDegree ≤ (map φ f).totalDegree := by
    by_contra h
    exact htop.ne_zero (homogeneousComponent_eq_zero _ _ (by omega))
  have he := le_antisymm (totalDegree_map_le _ _) hge
  rw [← he] at htop
  have hf0 : map φ f ≠ 0 := fun hz => htop.ne_zero (by rw [hz, map_zero])
  refine ⟨he, fun hu => ?_, fun g h hgh => ?_⟩
  · have hd := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    have heq := totalDegree_eq_zero_iff_eq_C.mp hd
    apply htop.not_isUnit
    rw [hd, homogeneousComponent_zero]
    rwa [heq] at hu
  · have hg : g ≠ 0 := fun hz => hf0 (by rw [hgh, hz, zero_mul])
    have hh : h ≠ 0 := fun hz => hf0 (by rw [hgh, hz, mul_zero])
    have hprod : homogeneousComponent (map φ f).totalDegree (map φ f) =
        homogeneousComponent g.totalDegree g * homogeneousComponent h.totalDegree h := by
      rw [hgh, totalDegree_mul_of_isDomain hg hh, top_homogeneousComponent_mul]
    exact (htop.isUnit_or_isUnit hprod).imp (hunit g) (hunit h)

end
end CCDN
