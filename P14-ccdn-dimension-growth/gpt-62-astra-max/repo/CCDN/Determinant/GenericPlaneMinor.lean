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
import CCDN.Noether.ClosedFormKernel
import CCDN.Noether.ShearNormalization

/-! Construct the generic minor over the slope ring via its fraction field. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {K F σ : Type*} [Field K] (d : ℕ) (hd : 0 < d) (f : MvPolynomial (Option σ) K)
    (hf : Irreducible f) (hm : (optionEquivLeft K σ f).Monic)
    (hdeg : (optionEquivLeft K σ f).natDegree = d)

private lemma genericPlaneMap_totalDegree_le [Field F]
    [Algebra K F] [Algebra (MvPolynomial σ K) F]
    (f : MvPolynomial (Option σ) K) :
    (genericPlaneMap K F σ f).totalDegree ≤ f.totalDegree := by
  apply linear_eval₂_totalDegree_le _ _ _ f
  intro i
  cases i with
  | none => simp
  | some i => exact (totalDegree_mul _ _).trans (by simp)

include hd hf hm hdeg in
/-- Over the fraction field of the slope ring, the generic plane of a positioned irreducible
equation with a smooth origin is irreducible, smooth at the origin in the first coordinate,
and monic of the same outer degree. -/
lemma genericPlaneMap_smooth_monic
    (hz : eval (0 : Option σ → K) f = 0)
    (hs : eval (0 : Option σ → K) (pderiv none f) ≠ 0) :
    Irreducible (genericPlaneMap K (FractionRing (MvPolynomial σ K)) σ f) ∧
      eval 0 (genericPlaneMap K (FractionRing (MvPolynomial σ K)) σ f) = 0 ∧
      eval 0 (pderiv 0 (genericPlaneMap K (FractionRing (MvPolynomial σ K)) σ f)) ≠ 0 ∧
      (bivariatePolynomialEquiv _
        (genericPlaneMap K (FractionRing (MvPolynomial σ K)) σ f)).natDegree = d := by
  let φ := algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
  have hx := hdeg ▸ hd
  have hpos := by
    rw [natDegree_optionEquivLeft] at hx
    exact hx.trans_le (degreeOf_le_totalDegree f none)
  refine ⟨genericPlaneMap_irreducible f hf hpos hm hx, ?_, ?_, ?_⟩
  · rw [genericPlaneMap_eval_zero, hz, map_zero]
  · rw [genericPlaneMap_pderiv, genericPlaneMap_eval_zero]
    aesop
  · rw [genericPlaneMap_bivariate, bivariateMap_natDegree_of_monic φ
      (genericPlanePolynomial_monic f hm), genericPlanePolynomial_natDegree f hm, hdeg]

include hd hf hm hdeg in
/-- In characteristic zero or greater than 2*d^2, a positioned irreducible hypersurface
with a smooth origin supplies a nonzero minor polynomial in its plane slopes. -/
theorem exists_genericPlane_minor
    (htotal : f.totalDegree ≤ d) (hchar : CharZeroOrGT K (2 * d ^ 2))
    (hz : eval (0 : Option σ → K) f = 0)
    (hs : eval (0 : Option σ → K) (pderiv none f) ≠ 0) :
    (closedFormCoefficientMatrix d (genericPlanePolynomial f)).HasNonzeroMinor
      (2 * d ^ 2 - 1) := by
  obtain ⟨hgi, hgz, hgs, hgd⟩ := genericPlaneMap_smooth_monic d hd f hf hm hdeg hz hs
  obtain ⟨a, c, hdet⟩ := minor_of_smooth_point d _ hgi 0
    hgz hgs hgd ((genericPlaneMap_totalDegree_le f).trans htotal)
    (hchar.map (algebraMap K (FractionRing (MvPolynomial σ K))))
  refine ⟨a, c, fun he ↦ hdet ?_⟩
  simp [genericPlaneMap_bivariate, ← closedForm_minor_map, he]

end
end CCDN
