/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.CharZeroOrGT
public import CCDN.Noether.BivariateClosedForms
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
import CCDN.Determinant.ResidueEliminantEvaluation
import CCDN.ForMathlib.Polynomial
import CCDN.Noether.DifferentialConstantRelation
import CCDN.Noether.DifferentialResidue
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Etale.Field

/-! A bounded closed form for a monic irreducible bivariate equation is
proportional to the gradient. The residue is differentially constant in the
separable root extension and descends to the base by elimination. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Differential
open scoped Differential
attribute [local instance] rationalDifferential

section

variable {F : Type*} [Field F] [IsAlgClosed F]
  (f g h : F[X][X]) (hf : Irreducible f) (hm : f.Monic)
  (hgdeg : g.natDegree < f.natDegree) (hhdeg : h.natDegree < f.natDegree)
  (D : ℕ) (hfD : ∀ i, (f.coeff i).natDegree ≤ D) (hgD : ∀ i, (g.coeff i).natDegree ≤ D)
  (hmchar : CharZeroOrGT F f.natDegree)
  (hchar : CharZeroOrGT F ((f.natDegree + (f.natDegree - 1)) * D))
  (hclosed : (bivariateCoefficientDerivative F) g * f -
  g * (bivariateCoefficientDerivative F) f = h.derivative * f - h * f.derivative)
include F f g h hf hm hgdeg hhdeg D hfD hgD hmchar hchar hclosed

/-- Over the algebraically closed base field, closed forms with the indicated
bounds are constant multiples of the gradient. -/
theorem bivariate_closed_form_eq_gradient :
    ∃ a : F, g = C (C a) * f.derivative ∧
      h = C (C a) * (bivariateCoefficientDerivative F) f := by
  let φ := algebraMap F[X] (RatFunc F)
  let fr := f.map φ
  let gr := g.map φ
  let hr := h.map φ
  have hinj := RatFunc.algebraMap_injective F
  have hfr : Irreducible fr := (hm.irreducible_iff_irreducible_map_fraction_map).mp hf
  have hfm : fr.Monic := hm.map φ
  have hfd := natDegree_map_eq_of_injective hinj f
  have hcharR := hmchar.map (algebraMap F (RatFunc F))
  have hsep : fr.Separable := (separable_iff_derivative_ne_zero hfr).mpr
    (derivative_ne_zero_of_natCast_natDegree_ne_zero
      (hcharR.natCast_ne_zero hfr.natDegree_pos.ne' hfd.le))
  let : Fact (Irreducible fr) := ⟨hfr⟩
  let β := AdjoinRoot.root fr
  have hβ : aeval β fr = 0 := by simp [β]
  have hs := hsep.aeval_derivative_ne_zero hβ
  have hsepβ : IsSeparable (RatFunc F) β := by
    simpa [IsSeparable, β, AdjoinRoot.minpoly_root hfr.ne_zero, hfm.leadingCoeff] using hsep
  have hle : (⊤ : Subalgebra (RatFunc F) (AdjoinRoot fr)) ≤ (separableClosure _ _).toSubalgebra := by
    rw [← AdjoinRoot.adjoinRoot_eq_top (f := fr)]
    exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr (mem_separableClosure_iff.mpr hsepβ))
  let : Algebra.IsSeparable (RatFunc F) (AdjoinRoot fr) :=
    ⟨fun x => mem_separableClosure_iff.mp (hle (show x ∈ (⊤ : Subalgebra _ _) by simp))⟩
  let := Algebra.FormallyEtale.of_isSeparable (RatFunc F) (AdjoinRoot fr)
  let := etaleDifferential (RatFunc F) (AdjoinRoot fr)
  let := etaleDifferential_algebra (RatFunc F) (AdjoinRoot fr)
  have hc : Differential.mapCoeffs gr * fr - gr * Differential.mapCoeffs fr =
      hr.derivative * fr - hr * fr.derivative := by
    simpa only [φ, fr, gr, hr, Polynomial.map_sub, Polynomial.map_mul, derivative_map,
      bivariateCoefficientDerivative_map] using congrArg (Polynomial.map φ) hclosed
  let ψ := algebraMap (RatFunc F) (AdjoinRoot fr)
  let t := ψ RatFunc.X
  have hmapp : (aeval t).toRingHom = ψ.comp φ := RingHom.ext fun p => by
    change aeval t p = ψ (φ p)
    rw [show t = algebraMap (RatFunc F) (AdjoinRoot fr) RatFunc.X by rfl,
      aeval_algebraMap_apply, RatFunc.aeval_X_left_eq_algebraMap]
  have hA (p : F[X][X]) : (p.map (aeval t).toRingHom).eval β = aeval β (p.map φ) := by
    rw [hmapp, ← Polynomial.map_map, eval_map, aeval_def]
  have hA' : (f.map (aeval t).toRingHom).derivative.eval β = aeval β fr.derivative := by
    simpa only [derivative_map, fr] using hA f.derivative
  have hres : aeval β gr / aeval β fr.derivative ∈ (algebraMap F (AdjoinRoot fr)).range := by
    by_cases hg : g = 0
    · simp [gr, hg]
    have hD := closed_form_residue_deriv_eq_zero fr gr hr β hβ hs hc
    have ht : t′ = 1 := by
      change (algebraMap (RatFunc F) (AdjoinRoot fr) RatFunc.X)′ = 1
      rw [deriv_algebraMap, ← RatFunc.algebraMap_X, rationalDerivative_polynomial]
      simp
    have hbase (a : F) : (algebraMap F (AdjoinRoot fr) a)′ = 0 := by
      rw [IsScalarTower.algebraMap_apply F (RatFunc F), deriv_algebraMap, RatFunc.algebraMap_eq_C]
      simp [← RatFunc.algebraMap_C]
    apply differential_constant_mem_base_of_relation hbase t _ ht hD (residueEliminant f g)
      (residueEliminant_ne_zero f g hfr hg hgdeg)
      ((hchar.map (algebraMap F (AdjoinRoot fr))).mono (residueEliminant_natDegree_le f g D hfD hgD))
    have hrel := residueEliminant_eval_ratio_eq_zero t β f g hgdeg
      ((hA f).trans hβ) (hA'.trans_ne hs)
    dsimp only at hrel
    rwa [hA g, hA'] at hrel
  have hd (q : F[X][X]) (hq : q.natDegree < f.natDegree) : (q.map φ).degree < fr.degree := by
    rw [degree_map_eq_of_injective hinj, degree_eq_natDegree hfr.ne_zero, hfd]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast hq)
  obtain ⟨a, ha, hb⟩ := closed_form_eq_constant_gradient_of_residue_mem_base fr gr hr hfr hfm β
    hβ hs (hd g hgdeg) (hd h hhdeg) hc hres
  refine ⟨a, Polynomial.map_injective φ hinj ?_, Polynomial.map_injective φ hinj ?_⟩
  · simpa [φ, gr, fr, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C, derivative_map] using ha
  · simpa [φ, hr, fr, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C, bivariateCoefficientDerivative_map] using hb

end
end
end CCDN
