/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Noether.EulerClosedFormRank
import CCDN.ForMathlib.MvPolynomial
import CCDN.Hilbert.HomogeneousHilbert
import CCDN.Noether.ShearNormalization

/-! The explicit Euler parameters exhaust all polynomial pairs satisfying
the degree and Euler-contraction constraints. -/

namespace CCDN
section
open MvPolynomial

lemma totalDegree_sub_top_component_le {R σ : Type*} [CommRing R]
    (k : ℕ) (p : MvPolynomial σ R) (hp : p.totalDegree ≤ k + 1) :
    (p - homogeneousComponent (k + 1) p).totalDegree ≤ k := by
  apply Finset.sup_le
  intro m hm
  have hm0 := mem_support_iff.mp hm
  rw [coeff_sub, coeff_homogeneousComponent] at hm0
  by_cases he : m.degree = k + 1
  · grind
  · simp only [he, ite_false, sub_zero] at hm0
    have hle := (le_totalDegree (mem_support_iff.mpr hm0)).trans hp
    change m.degree ≤ k
    change m.degree ≤ k + 1 at hle
    omega

variable {F : Type*} [Field F] (k : ℕ)

/-- Every pair of bivariate polynomials of total degree at most `k + 1` whose radial contraction
also has total degree at most `k + 1` comes from an element of `EulerPairSpace F k`. -/
theorem exists_eulerBivariatePair
    (p q : Polynomial (Polynomial F))
    (hp : bivariateTotalDegree p ≤ k + 1)
    (hq : bivariateTotalDegree q ≤ k + 1)
    (he : bivariateTotalDegree (bivariateEulerContraction F (p, q)) ≤ k + 1) :
    ∃ u : EulerPairSpace F k, eulerBivariatePair F k u = (p, q) := by
  let e := bivariatePolynomialEquiv F
  have he' : (X 0 * e.symm p + X 1 * e.symm q).totalDegree ≤ k + 1 := by
    have hh : e (X 0 * e.symm p + X 1 * e.symm q) =
        bivariateEulerContraction F (p, q) := by
      simp [map_add, map_mul, AlgEquiv.apply_symm_apply,
        bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_X_one,
        bivariateEulerContraction, LinearMap.coe_mk, AddHom.coe_mk, e]
    rw [← hh] at he
    simpa [bivariateTotalDegree, e, AlgEquiv.symm_apply_apply] using he
  obtain ⟨u, hu⟩ : ∃ u : EulerPairSpace F k, eulerPairCoordinates F k u = ((e.symm p), (e.symm q)) := by
    let P := homogeneousComponent (k + 1) (e.symm p)
    let Q := homogeneousComponent (k + 1) (e.symm q)
    have htop : X 0 * P + X 1 * Q = 0 := by
      have hh := homogeneousComponent_eq_zero (k + 2) (X 0 * (e.symm p) + X 1 * (e.symm q)) (by omega)
      rw [map_add, show k + 2 = 1 + (k + 1) by omega,
        homogeneousComponent_mul_of_isHomogeneous_left (isHomogeneous_X F (0 : Fin 2)),
        homogeneousComponent_mul_of_isHomogeneous_left (isHomogeneous_X F (1 : Fin 2))] at hh
      exact hh
    obtain ⟨r, hr⟩ := (by
      have hh : X (1 : Fin 2) ∣ X 0 * P := by
        rw [show X 0 * P = -(X 1 * Q) by linear_combination htop]
        simp_all
      exact (X_dvd_mul_iff.mp hh).resolve_left (by simp_all))
    have hrhom : r.IsHomogeneous k := by
      have hh := homogeneous_multiplier (isHomogeneous_X F (1 : Fin 2))
        (X_ne_zero (1 : Fin 2))
        (show (X 1 * r).IsHomogeneous (k + 1) from
          hr ▸ homogeneousComponent_isHomogeneous (k + 1) (e.symm p))
        (by omega)
      grind
    have hQ : Q = -(X 0 * r) := by
      apply mul_left_cancel₀ (X_ne_zero (1 : Fin 2))
      grind
    let u : EulerPairSpace F k :=
      (⟨(e.symm p) - P, (mem_restrictTotalDegree _ _ _).mpr (totalDegree_sub_top_component_le k (e.symm p) hp)⟩,
       ⟨(e.symm q) - Q, (mem_restrictTotalDegree _ _ _).mpr (totalDegree_sub_top_component_le k (e.symm q) hq)⟩,
       ⟨r, hrhom⟩)
    refine ⟨u, ?_⟩
    apply Prod.ext
    · change (e.symm p) - P + X 1 * r = (e.symm p)
      grind
    · change (e.symm q) - Q - X 0 * r = (e.symm q)
      grind
  refine ⟨u, ?_⟩
  change (e (eulerPairCoordinates F k u).1, e (eulerPairCoordinates F k u).2) = (p, q)
  rw [hu]
  simp

