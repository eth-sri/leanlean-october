/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.EulerClosedFormRank
import CCDN.ForMathlib.MvPolynomial
import CCDN.Hilbert.HomogeneousHilbert
import CCDN.Noether.ShearNormalization

/-! The explicit Euler parameters exhaust all polynomial pairs satisfying
the degree and Euler-contraction constraints. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Every pair of bivariate polynomials of total degree at most `k + 1` whose radial contraction
also has total degree at most `k + 1` comes from an element of `EulerPairSpace F k`. -/
theorem exists_eulerBivariatePair {F : Type*} [Field F]
    (k : ℕ) (p q : Polynomial (Polynomial F))
    (hp : bivariateTotalDegree p ≤ k + 1)
    (hq : bivariateTotalDegree q ≤ k + 1)
    (he : bivariateTotalDegree (bivariateEulerContraction F (p, q)) ≤ k + 1) :
    ∃ u : EulerPairSpace F k, eulerBivariatePair F k u = (p, q) := by
  classical
  have hsub_le (g : MvPolynomial (Fin 2) F) (hg : g.totalDegree ≤ k + 1) :
      (g - homogeneousComponent (k + 1) g).totalDegree ≤ k :=
    Finset.sup_le fun m hm => by
      have hm0 := mem_support_iff.mp hm
      rw [coeff_sub, coeff_homogeneousComponent] at hm0
      by_cases heq : m.degree = k + 1
      · simp only [heq, ite_true, sub_self, ne_eq, not_true_eq_false] at hm0
      · simp only [heq, ite_false, sub_zero] at hm0
        have hle := (le_totalDegree (mem_support_iff.mpr hm0)).trans hg
        change m.degree ≤ k; change m.degree ≤ k + 1 at hle; omega
  let e := bivariatePolynomialEquiv F
  let p' := e.symm p
  let q' := e.symm q
  have he' : (X 0 * p' + X 1 * q').totalDegree ≤ k + 1 := by
    have hh : e (X 0 * p' + X 1 * q') = bivariateEulerContraction F (p, q) := by
      simp only [map_add, map_mul, AlgEquiv.apply_symm_apply,
        bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_X_one,
        bivariateEulerContraction, LinearMap.coe_mk, AddHom.coe_mk, e, p', q']
    rw [← hh] at he
    simpa only [bivariateTotalDegree, e, AlgEquiv.symm_apply_apply] using he
  let P := homogeneousComponent (k + 1) p'
  let Q := homogeneousComponent (k + 1) q'
  have htop : X 0 * P + X 1 * Q = 0 := by
    have hh := homogeneousComponent_eq_zero (k + 2) (X 0 * p' + X 1 * q') (by omega)
    rwa [map_add, show k + 2 = 1 + (k + 1) by omega,
      homogeneousComponent_mul_of_isHomogeneous_left (isHomogeneous_X F (0 : Fin 2)),
      homogeneousComponent_mul_of_isHomogeneous_left (isHomogeneous_X F (1 : Fin 2))] at hh
  have hdiv : X (1 : Fin 2) ∣ P := by
    have hh : X (1 : Fin 2) ∣ X 0 * P := by
      rw [show X 0 * P = -(X 1 * Q) by linear_combination htop]
      exact dvd_neg.mpr (dvd_mul_right _ _)
    exact (X_dvd_mul_iff.mp hh).resolve_left (by rw [X_dvd_X]; decide)
  obtain ⟨r, hr⟩ := hdiv
  have hrhom : r.IsHomogeneous k := by
    have hh := homogeneous_multiplier (isHomogeneous_X F (1 : Fin 2)) (X_ne_zero (1 : Fin 2))
      (show (X 1 * r).IsHomogeneous (k + 1) from hr ▸ homogeneousComponent_isHomogeneous (k + 1) p')
      (by omega)
    simpa only [Nat.add_sub_cancel] using hh
  have hQ : Q = -(X 0 * r) := by
    apply mul_left_cancel₀ (X_ne_zero (1 : Fin 2))
    rw [hr] at htop; linear_combination htop
  let u : EulerPairSpace F k :=
    (⟨p' - P, (mem_restrictTotalDegree _ _ _).mpr (hsub_le p' hp)⟩,
     ⟨q' - Q, (mem_restrictTotalDegree _ _ _).mpr (hsub_le q' hq)⟩,
     ⟨r, hrhom⟩)
  have hu : eulerPairCoordinates F k u = (p', q') := Prod.ext
    (by change p' - P + X 1 * r = p'; rw [← hr]; ring)
    (by change q' - Q - X 0 * r = q'; rw [hQ]; ring)
  refine ⟨u, ?_⟩
  change (e (eulerPairCoordinates F k u).1, e (eulerPairCoordinates F k u).2) = (p, q)
  rw [hu]
  simp only [p', q', AlgEquiv.apply_symm_apply]

end
end CCDN
