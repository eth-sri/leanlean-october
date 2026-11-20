/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.CharZeroOrGT
public import CCDN.Determinant.GenericPlaneSmoothness
public import CCDN.ForMathlib.Matrix
import CCDN.Determinant.ClosedFormIntegerMinor
import CCDN.Determinant.PlaneMultiplicity
import CCDN.Noether.ClosedFormScaling
import CCDN.Noether.FormalBranchBaseChange
import CCDN.Noether.ShearNormalization

/-!
A nonzero polynomial determinant in the generic slope parameters. For a
positioned irreducible equation with a smooth origin, the minor is constructed
over the parameter polynomial ring, by descent from its fraction field.

A smooth rational point supplies a nonzero closed-form coefficient minor
for an irreducible plane equation in characteristic zero or large characteristic.
The base field need not be algebraically closed.

A smooth rational point on an irreducible plane curve implies geometric
irreducibility. The proof uses the faithful formal branch, extends its
coordinate algebra to every field, and identifies the resulting prime ideal
in the polynomial ring over that field.
-/

@[expose] public section
namespace CCDN
noncomputable section
open scoped TensorProduct

/-- An irreducible plane equation with a smooth rational point remains
irreducible over every extension field. The base field need not be perfect. -/
theorem irreducible_map_of_smooth_plane_point
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (z : Fin 2 → K) (j : Fin 2)
    (hz : MvPolynomial.eval z f = 0)
    (hj : MvPolynomial.eval z (MvPolynomial.pderiv j f) ≠ 0) :
    Irreducible (MvPolynomial.map (algebraMap K L) f) := by
  let I := Ideal.span {f}
  let J : Ideal (L ⊗[K] MvPolynomial (Fin 2) K) :=
    I.map Algebra.TensorProduct.includeRight
  let e := Algebra.TensorProduct.tensorQuotientEquiv (R := K) L
    (MvPolynomial (Fin 2) K) L I
  have : IsDomain (L ⊗[K] (MvPolynomial (Fin 2) K ⧸ I)) :=
    isDomain_tensor_plane_quotient_of_smooth_point f hf z j hz hj
  have : IsDomain ((L ⊗[K] MvPolynomial (Fin 2) K) ⧸ J) :=
    Function.Injective.isDomain e.symm e.symm.injective
  have : J.IsPrime := (Ideal.Quotient.isDomain_iff_prime J).mp inferInstance
  let E := MvPolynomial.algebraTensorAlgEquiv (σ := Fin 2) K L
  have hmap : J.map E = Ideal.span {MvPolynomial.map (algebraMap K L) f} := by
    simp_all [J, I, Ideal.map_span, Set.image_singleton, E]
  have hp : (Ideal.span {MvPolynomial.map (algebraMap K L) f}).IsPrime := by
    rw [← hmap]
    infer_instance
  have hne : MvPolynomial.map (algebraMap K L) f ≠ 0 := by
    exact (map_ne_zero_iff _ (MvPolynomial.map_injective _ (algebraMap K L).injective)).mpr
      hf.ne_zero
  exact ((Ideal.span_singleton_prime hne).mp hp).irreducible

end
end CCDN

namespace CCDN
noncomputable section
open Polynomial Matrix

/-- A nonzero minor over the original coefficient field, obtained by proving
geometric irreducibility from the smooth point. -/
private theorem exists_closedForm_minor_of_smooth_plane_point
    {K : Type*} [Field K]
    (d : ℕ) (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (z : Fin 2 → K) (j : Fin 2)
    (hz : MvPolynomial.eval z f = 0)
    (hj : MvPolynomial.eval z (MvPolynomial.pderiv j f) ≠ 0)
    (hm : (bivariatePolynomialEquiv K f).Monic)
    (hdeg : (bivariatePolynomialEquiv K f).natDegree = d)
    (htotal : f.totalDegree ≤ d) (hchar : CharZeroOrGT K (2 * d ^ 2)) :
    (closedFormCoefficientMatrix d (bivariatePolynomialEquiv K f)).HasNonzeroMinor
      (2 * d ^ 2 - 1) := by
  let L := AlgebraicClosure K
  let φ := algebraMap K L
  let g := bivariateMap φ (bivariatePolynomialEquiv K f)
  have hgi : Irreducible g := by
    dsimp only [g]
    rw [bivariatePolynomialEquiv_map, MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv L)]
    exact irreducible_map_of_smooth_plane_point f hf z j hz hj
  have hgm : g.Monic := bivariateMap_monic φ hm
  have hgd : g.degree = d := by
    rw [degree_eq_natDegree hgm.ne_zero, bivariateMap_natDegree_of_monic φ hm, hdeg]
  have hgt : bivariateTotalDegree g ≤ d := by
    apply (bivariateTotalDegree_map_le φ _).trans
    simpa [bivariateTotalDegree, AlgEquiv.symm_apply_apply] using htotal
  have hr := closedForm_coefficient_rank_lower d g hgi hgm hgd d hgt
    ((hchar.map φ).mono (by linarith))
  exact hasNonzeroMinor_of_bivariateMap φ
    (Matrix.hasNonzeroMinor_of_le_rank (closedFormCoefficientMatrix d g) (by omega))

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

private lemma genericPlaneMap_totalDegree_le {K F σ : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (MvPolynomial σ K) F]
    (f : MvPolynomial (Option σ) K) :
    (genericPlaneMap K F σ f).totalDegree ≤ f.totalDegree := by
  apply linear_eval₂_totalDegree_le _ _ _ f
  intro i
  cases i with
  | none => simp
  | some i => exact (totalDegree_mul _ _).trans (by simp)

section

variable {K σ : Type*} [Field K]
  (d : ℕ) (hd : 0 < d) (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
  (hm : (optionEquivLeft K σ f).Monic)
  (hdeg : (optionEquivLeft K σ f).natDegree = d)
include K σ d hd f hf hm hdeg

/-- In characteristic zero or greater than 2*d^2, a positioned irreducible hypersurface
with a smooth origin supplies a nonzero minor polynomial in its plane slopes. -/
theorem exists_genericPlane_minor
    (htotal : f.totalDegree ≤ d) (hchar : CharZeroOrGT K (2 * d ^ 2))
    (hz : eval (0 : Option σ → K) f = 0)
    (hs : eval (0 : Option σ → K) (pderiv none f) ≠ 0) :
    (closedFormCoefficientMatrix d (genericPlanePolynomial f)).HasNonzeroMinor
      (2 * d ^ 2 - 1) := by
  let F := FractionRing (MvPolynomial σ K)
  let φ := algebraMap (MvPolynomial σ K) F
  let g := genericPlaneMap K F σ f
  have hg : bivariatePolynomialEquiv F g = bivariateMap φ (genericPlanePolynomial f) :=
    genericPlaneMap_bivariate f
  have hmonic := genericPlanePolynomial_monic f hm
  apply hasNonzeroMinor_of_bivariateMap φ
  rw [← hg]
  refine exists_closedForm_minor_of_smooth_plane_point d g
    (genericPlaneMap_irreducible f hf hm (hdeg ▸ hd)) 0 0 ?_ ?_ ?_ ?_
    ((genericPlaneMap_totalDegree_le f).trans htotal) (hchar.map (algebraMap K F))
  · rw [show g = genericPlaneMap K F σ f from rfl, genericPlaneMap_eval_zero, hz, map_zero]
  · simpa only [g, genericPlaneMap_pderiv, genericPlaneMap_eval_zero] using
      (map_ne_zero (algebraMap K F)).mpr hs
  · rw [hg]
    exact bivariateMap_monic φ hmonic
  · rw [hg, bivariateMap_natDegree_of_monic φ hmonic, genericPlanePolynomial_natDegree f hm, hdeg]

end

end
end CCDN
