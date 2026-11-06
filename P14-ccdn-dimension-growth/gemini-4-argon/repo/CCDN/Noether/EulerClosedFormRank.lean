/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.BivariateTotalDegree
public import CCDN.Noether.EulerClosedForms
public import CCDN.Noether.EulerPairSpace
import CCDN.Noether.ClosedFormScaling
import CCDN.Noether.ShearNormalization

/-! The Euler-constrained closed-form operator has full rank d^2-1 for
irreducible bivariate equations of full outer degree in characteristic zero. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

/-- The explicit Euler pair, in the nested polynomial ring used by the
closed-form classification. -/
def eulerBivariatePair (R : Type*) [CommRing R] (k : ℕ) :
    EulerPairSpace R k →ₗ[R] R[X][X] × R[X][X] :=
  ((bivariatePolynomialEquiv R).toLinearMap.prodMap
    (bivariatePolynomialEquiv R).toLinearMap).comp (eulerPairCoordinates R k)

/-- Closed-form operator on exactly d^2-1 explicit polynomial parameters. -/
def eulerClosedFormOperator {R : Type*} [CommRing R] (k : ℕ) (f : R[X][X]) :
    EulerPairSpace R k →ₗ[R] R[X][X] :=
  (closedFormOperator f).comp (eulerBivariatePair R k)

/-- Over an algebraically closed field of characteristic zero, the Euler closed-form operator of
an irreducible `f` of outer degree `k + 2` whose outer leading coefficient is a nonzero constant
is injective. Scalar normalization changes neither the domain nor injectivity. -/
theorem eulerClosedFormOperator_injective_of_constant_leading
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (k : ℕ) (f : F[X][X]) (hf : Irreducible f) (a : F) (ha : a ≠ 0)
    (hl : f.leadingCoeff = C a) (hdeg : f.natDegree = k + 2) :
    Function.Injective (eulerClosedFormOperator k f) := by
  let g := a⁻¹ • f
  have hm := bivariate_monic_normalize a ha f hl
  have hi := (bivariate_irreducible_smul_iff a⁻¹ (inv_ne_zero ha) f).mpr hf
  have hd : g.natDegree = k + 2 := by rw [natDegree_smul f (inv_ne_zero ha), hdeg]
  intro u v huv
  have hsub : eulerClosedFormOperator k g (u - v) = 0 := by
    rw [map_sub, sub_eq_zero]
    change closedFormOperator (a⁻¹ • f) (eulerBivariatePair F k u) =
      closedFormOperator (a⁻¹ • f) (eulerBivariatePair F k v)
    rw [closedFormOperator_smul_equation, closedFormOperator_smul_equation]
    exact congrArg (a⁻¹ • ·) huv
  let w := u - v
  let p := (eulerBivariatePair F k w).1
  let q := (eulerBivariatePair F k w).2
  have hfst : bivariateTotalDegree p ≤ k + 1 := by
    change ((bivariatePolynomialEquiv F).symm
      (bivariatePolynomialEquiv F (eulerPairCoordinates F k w).1)).totalDegree ≤ _
    rw [AlgEquiv.symm_apply_apply]; exact eulerPairCoordinates_fst_degree k w
  have hsnd : bivariateTotalDegree q ≤ k + 1 := by
    change ((bivariatePolynomialEquiv F).symm
      (bivariatePolynomialEquiv F (eulerPairCoordinates F k w).2)).totalDegree ≤ _
    rw [AlgEquiv.symm_apply_apply]; exact eulerPairCoordinates_snd_degree k w
  have hp : p.degree < g.degree := by
    rw [degree_eq_natDegree hi.ne_zero, hd]
    exact degree_le_natDegree.trans_lt
      (mod_cast ((bivariate_natDegree_le_totalDegree p).trans hfst).trans_lt (by omega))
  have hq : q.degree < g.degree := by
    rw [degree_eq_natDegree hi.ne_zero, hd]
    exact degree_le_natDegree.trans_lt
      (mod_cast ((bivariate_natDegree_le_totalDegree q).trans hsnd).trans_lt (by omega))
  have hcontr : bivariateTotalDegree (bivariateEulerContraction F (eulerBivariatePair F k w)) ≤ k + 1 := by
    simp only [bivariateEulerContraction, eulerBivariatePair, LinearMap.comp_apply,
      LinearMap.prodMap_apply, AlgEquiv.toLinearMap_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← bivariatePolynomialEquiv_X_zero, ← bivariatePolynomialEquiv_X_one,
      ← map_mul, ← map_mul, ← map_add]
    change ((bivariatePolynomialEquiv F).symm (bivariatePolynomialEquiv F _)).totalDegree ≤ _
    rw [AlgEquiv.symm_apply_apply]; exact eulerPairCoordinates_contraction_degree k w
  have he : (bivariateEulerContraction F (p, q)).coeff g.natDegree = 0 :=
    coeff_eq_zero_of_natDegree_lt
      (((bivariate_natDegree_le_totalDegree _).trans hcontr).trans_lt (by omega))
  obtain ⟨hp0, hq0⟩ := bivariate_euler_closed_form_eq_zero g p q hi hm (by omega) hp hq hsub he
  have hw0 : w = 0 := eulerPairCoordinates_injective k <| Prod.ext
    ((bivariatePolynomialEquiv F).injective (by
      simpa only [p, eulerBivariatePair, LinearMap.comp_apply, LinearMap.prodMap_apply,
        AlgEquiv.toLinearMap_apply, Prod.fst_zero, map_zero] using hp0))
    ((bivariatePolynomialEquiv F).injective (by
      simpa only [q, eulerBivariatePair, LinearMap.comp_apply, LinearMap.prodMap_apply,
        AlgEquiv.toLinearMap_apply, Prod.snd_zero, map_zero] using hq0))
  exact sub_eq_zero.mp hw0

end
end CCDN
