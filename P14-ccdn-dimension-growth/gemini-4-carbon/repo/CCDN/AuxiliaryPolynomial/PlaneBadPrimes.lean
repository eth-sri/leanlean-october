/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Analysis.PrimeCutoff
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadReduction
public import CCDN.Height.IntegerCoefficientHeight
public import CCDN.Noether.BivariateTotalDegree
public import CCDN.Plane.FiniteFieldConstants
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Nilpotent

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma mvPolynomial_irreducible_of_field_map
    {F K σ : Type*} [Field F] [Field K] (φ : F →+* K)
    (f : MvPolynomial σ F) (hf : Irreducible (MvPolynomial.map φ f)) : Irreducible f := by
  have hunit (q : MvPolynomial σ F) (hq : IsUnit (MvPolynomial.map φ q)) : IsUnit q := by
    obtain ⟨hc, hd⟩ := MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hq
    have he : (MvPolynomial.map φ q).totalDegree = q.totalDegree :=
      MvPolynomial.totalDegree_map_of_injective φ.injective q
    exact MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mpr
      ⟨isUnit_iff_ne_zero.mpr fun hz => hc.ne_zero (by rw [coeff_map, hz, map_zero]), he ▸ hd⟩
  exact ⟨fun h => hf.not_isUnit (h.map (MvPolynomial.map φ)),
    fun g h he => (hf.isUnit_or_isUnit (by rw [he, map_mul])).imp (hunit g) (hunit h)⟩

lemma bivariateTotalDegree_equiv {R : Type*} [CommRing R] (f : MvPolynomial (Fin 2) R) :
    bivariateTotalDegree (bivariatePolynomialEquiv R f) = f.totalDegree := by
  simp only [bivariateTotalDegree, AlgEquiv.symm_apply_apply]

end
end CCDN
