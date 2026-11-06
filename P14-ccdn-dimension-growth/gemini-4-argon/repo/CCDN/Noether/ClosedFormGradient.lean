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

/-!
The monic irreducible closed-form criterion, in characteristic zero or in
characteristic larger than the displayed degree bounds. Separability, the
differential root extension and constant-residue descent are all constructed
from the polynomial and the degree bounds.

Constant residues in characteristic zero or large characteristic. The nonzero
annihilating relation and its degree bound are constructed by a Sylvester
resultant.

Extend a differential structure to an explicitly separable monic root
extension in any characteristic. The construction is the implicit-derivative
quotient construction from Mathlib's characteristic-zero instance, with the
nonvanishing derivative supplied by separability.
-/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Differential
open scoped Differential
attribute [local instance] rationalDifferential

/-- The differential structure on `AdjoinRoot f` extending the derivation of `K`, for a monic
irreducible separable `f`: the root `α` is sent to `-(f^D)(α) / f'(α)`, where `f^D` is `f` with
its coefficients differentiated. -/
@[reducible]
def separableAdjoinRootDifferential {K : Type*} [Field K] [Differential K]
    (f : K[X]) [Fact (Irreducible f)] [Fact f.Monic] (hsep : f.Separable) :
    Differential (AdjoinRoot f) where
  deriv := Derivation.liftOfSurjective (f := (AdjoinRoot.mk f).toIntAlgHom) AdjoinRoot.mk_surjective
    (d := implicitDeriv <| AdjoinRoot.modByMonicHom Fact.out <|
      - (aeval (AdjoinRoot.root f) (Differential.mapCoeffs f)) /
        (aeval (AdjoinRoot.root f) f.derivative)) (by
      rintro x hx
      simp_all only [RingHom.toIntAlgHom_apply, AdjoinRoot.mk_eq_zero]
      obtain ⟨q, rfl⟩ := hx
      simp only [Derivation.leibniz, smul_eq_mul]
      refine dvd_add (dvd_mul_right ..) (dvd_mul_of_dvd_right ?_ _)
      rw [← AdjoinRoot.mk_eq_zero]
      unfold implicitDeriv
      simp only [AdjoinRoot.aeval_eq, Derivation.coe_add, Derivation.coe_smul, Pi.add_apply,
        Pi.smul_apply, Derivation.restrictScalars_apply, derivative'_apply, smul_eq_mul, map_add,
        map_mul, AdjoinRoot.mk_leftInverse Fact.out _]
      rw [div_mul_cancel₀, add_neg_cancel]
      have hc : aeval (AdjoinRoot.root f) f = 0 := by
        rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
      simpa only [AdjoinRoot.aeval_eq] using hsep.aeval_derivative_ne_zero hc)

-- Needed by `rw [Derivation.liftOfSurjective_apply]` below. With the default setting
-- (Lean v4.35.0) the rewrite fails: the pattern `(Derivation.liftOfSurjective ?hf ?hd) (?m ?x)`
-- is not found in `(Derivation.liftOfSurjective ⋯ ⋯) ((AdjoinRoot.mk f).toIntAlgHom (C a))`,
-- since matching `?m ?x` against the `toIntAlgHom` coercion needs unfolding past the
-- transparency that the unifier otherwise respects.
set_option backward.isDefEq.respectTransparency false in
private theorem separableAdjoinRootDifferential_algebra {K : Type*} [Field K] [Differential K]
    (f : K[X]) [Fact (Irreducible f)] [Fact f.Monic] (hsep : f.Separable) :
    let := separableAdjoinRootDifferential f hsep
    DifferentialAlgebra K (AdjoinRoot f) := by
  let := separableAdjoinRootDifferential f hsep
  refine { deriv_algebraMap := fun a => ?_ }
  change (Derivation.liftOfSurjective _ _) ((AdjoinRoot.mk f).toIntAlgHom (C a)) = _
  rw [Derivation.liftOfSurjective_apply, implicitDeriv_C]
  rfl

/-- Over an algebraically closed field `F` of characteristic zero or larger than the
degree bounds, a monic irreducible bivariate equation has only constant-gradient closed
forms within the strict outer-variable degree bounds. -/
theorem bivariate_closed_form_eq_gradient
    {F : Type*} [Field F] [IsAlgClosed F]
    (f g h : F[X][X]) (hf : Irreducible f) (hm : f.Monic)
    (hgdeg : g.natDegree < f.natDegree) (hhdeg : h.natDegree < f.natDegree)
    (D : ℕ) (hfD : ∀ i, (f.coeff i).natDegree ≤ D)
    (hgD : ∀ i, (g.coeff i).natDegree ≤ D)
    (hmchar : CharZeroOrGT F f.natDegree)
    (hchar : CharZeroOrGT F ((f.natDegree + (f.natDegree - 1)) * D))
    (hclosed : (bivariateCoefficientDerivative F) g * f -
        g * (bivariateCoefficientDerivative F) f = h.derivative * f - h * f.derivative) :
    ∃ a : F, g = C (C a) * f.derivative ∧
      h = C (C a) * (bivariateCoefficientDerivative F) f := by
  let φ := algebraMap F[X] (RatFunc F)
  let fr := f.map φ
  have hinj : Function.Injective φ := RatFunc.algebraMap_injective F
  have hfr : Irreducible fr := hm.irreducible_iff_irreducible_map_fraction_map.mp hf
  have hfd : fr.natDegree = f.natDegree := natDegree_map_eq_of_injective hinj f
  have hsep : fr.Separable := (separable_iff_derivative_ne_zero hfr).mpr
    (derivative_ne_zero_of_natCast_natDegree_ne_zero
      ((hfd ▸ hmchar.map (algebraMap F (RatFunc F))).natCast_ne_zero hfr.natDegree_pos.ne' le_rfl))
  let : Fact (Irreducible fr) := ⟨hfr⟩
  let : Fact fr.Monic := ⟨hm.map φ⟩
  let : Differential (AdjoinRoot fr) := separableAdjoinRootDifferential fr hsep
  have : DifferentialAlgebra (RatFunc F) (AdjoinRoot fr) :=
    separableAdjoinRootDifferential_algebra fr hsep
  let ψ := algebraMap (RatFunc F) (AdjoinRoot fr)
  let t : AdjoinRoot fr := ψ RatFunc.X
  let β : AdjoinRoot fr := AdjoinRoot.root fr
  have hβ : aeval β fr = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hs : aeval β fr.derivative ≠ 0 := hsep.aeval_derivative_ne_zero hβ
  have hclosed_rat : Differential.mapCoeffs (g.map φ) * f.map φ -
      g.map φ * Differential.mapCoeffs (f.map φ) =
      (h.map φ).derivative * f.map φ - h.map φ * (f.map φ).derivative := by
    rw [← bivariateCoefficientDerivative_map, ← bivariateCoefficientDerivative_map]
    simpa only [φ, Polynomial.map_sub, Polynomial.map_mul, derivative_map] using
      congrArg (Polynomial.map (algebraMap F[X] (RatFunc F))) hclosed
  have hmaps (q : F[X][X]) : q.map (aeval t).toRingHom = (q.map φ).map ψ := by
    ext i; simp only [coeff_map]
    change aeval t (q.coeff i) = ψ (φ (q.coeff i))
    induction q.coeff i using Polynomial.induction_on' with
    | add a b ha hb => simp only [map_add, ha, hb]
    | monomial n c =>
      simp only [t, ψ, φ, aeval_monomial, RatFunc.algebraMap_monomial, map_mul, map_pow,
        ← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply]
  have hrootL : ((f.map φ).map ψ).eval β = 0 := by simpa only [eval_map, aeval_def] using hβ
  have hsL : ((f.map φ).map ψ).derivative.eval β ≠ 0 := by
    simpa only [fr, derivative_map, eval_map, aeval_def] using hs
  have hder := closed_form_residue_deriv_eq_zero ((f.map φ).map ψ) ((g.map φ).map ψ)
    ((h.map φ).map ψ) β
    (by simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hrootL)
    (by simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hsL)
    (by
      dsimp only [ψ]
      simp only [differential_mapCoeffs_map, derivative_map]
      simpa only [Polynomial.map_sub, Polynomial.map_mul, derivative_map] using
        congrArg (Polynomial.map (algebraMap (RatFunc F) (AdjoinRoot fr))) hclosed_rat)
  have hres : aeval β (g.map φ) / aeval β fr.derivative ∈
      (algebraMap F (AdjoinRoot fr)).range := by
    by_cases hg0 : g = 0
    · simp only [hg0, Polynomial.map_zero, map_zero, zero_div]; exact ⟨0, map_zero _⟩
    · have hh := differential_constant_mem_base_of_relation
        (fun a => by
          rw [IsScalarTower.algebraMap_apply F (RatFunc F) (AdjoinRoot fr), deriv_algebraMap,
            show (algebraMap F (RatFunc F) a)′ = 0 by
              change rationalDerivative (algebraMap F (RatFunc F) a) = 0
              rw [IsScalarTower.algebraMap_apply F F[X] (RatFunc F), rationalDerivative_polynomial]
              simp, map_zero])
        t ((g.map (aeval t).toRingHom).eval β / (f.map (aeval t).toRingHom).derivative.eval β)
        (by
          rw [deriv_algebraMap, show (RatFunc.X : RatFunc F)′ = 1 by
            change rationalDerivative RatFunc.X = 1
            rw [← RatFunc.algebraMap_X, rationalDerivative_polynomial, derivative_X, map_one],
            map_one])
        (by simpa only [hmaps, aeval_def, Algebra.algebraMap_self, eval₂_id] using hder)
        (residueEliminant f g) (residueEliminant_ne_zero f g hfr hg0 hgdeg)
        ((hchar.map (algebraMap F (AdjoinRoot fr))).mono (residueEliminant_natDegree_le f g D hfD hgD))
        (residueEliminant_eval_ratio_eq_zero t β f g hgdeg
          (by simpa only [hmaps] using hrootL) (by simpa only [hmaps] using hsL))
      simpa only [fr, hmaps, ψ, derivative_map, eval_map, aeval_def] using hh
  have hdeg_lt (q : F[X][X]) (hq : q.natDegree < f.natDegree) : (q.map φ).degree < fr.degree := by
    rw [degree_eq_natDegree hfr.ne_zero]
    exact degree_le_natDegree.trans_lt
      (mod_cast (natDegree_map_eq_of_injective hinj q).trans_lt (hfd ▸ hq))
  obtain ⟨a, ha, hb⟩ := closed_form_eq_constant_gradient_of_residue_mem_base fr (g.map φ) (h.map φ)
    hfr (hm.map φ) β hβ hs (hdeg_lt g hgdeg) (hdeg_lt h hhdeg) hclosed_rat hres
  refine ⟨a, Polynomial.map_injective φ hinj ?_, Polynomial.map_injective φ hinj ?_⟩
  · simpa only [fr, φ, Polynomial.map_mul, Polynomial.map_C, RatFunc.algebraMap_C,
      RatFunc.algebraMap_eq_C, derivative_map] using ha
  · simpa only [fr, φ, Polynomial.map_mul, Polynomial.map_C, RatFunc.algebraMap_C,
      RatFunc.algebraMap_eq_C, bivariateCoefficientDerivative_map] using hb

end
end CCDN
