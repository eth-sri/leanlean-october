/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.CharZeroOrGT
import CCDN.Noether.BivariateClosedForms
import Mathlib.FieldTheory.RatFunc.AsPolynomial
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

namespace CCDN
noncomputable section
open Polynomial Differential
open scoped Differential

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
      apply dvd_add (dvd_mul_right ..)
      apply dvd_mul_of_dvd_right
      rw [← AdjoinRoot.mk_eq_zero]
      unfold implicitDeriv
      simp only [AdjoinRoot.aeval_eq, Derivation.coe_add, Derivation.coe_smul, Pi.add_apply,
        Pi.smul_apply, Derivation.restrictScalars_apply, derivative'_apply, smul_eq_mul, map_add,
        map_mul, AdjoinRoot.mk_leftInverse Fact.out _]
      rw [div_mul_cancel₀, add_neg_cancel]
      have hc : aeval (AdjoinRoot.root f) f = 0 := by
        rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
      simpa [AdjoinRoot.aeval_eq] using hsep.aeval_derivative_ne_zero hc)

-- Needed by `rw [Derivation.liftOfSurjective_apply]` below. With the default setting
-- (Lean v4.35.0) the rewrite fails: the pattern `(Derivation.liftOfSurjective ?hf ?hd) (?m ?x)`
-- is not found in `(Derivation.liftOfSurjective ⋯ ⋯) ((AdjoinRoot.mk f).toIntAlgHom (C a))`,
-- since matching `?m ?x` against the `toIntAlgHom` coercion needs unfolding past the
-- transparency that the unifier otherwise respects.
set_option backward.isDefEq.respectTransparency false in
theorem separableAdjoinRootDifferential_algebra {K : Type*} [Field K] [Differential K]
    (f : K[X]) [Fact (Irreducible f)] [Fact f.Monic] (hsep : f.Separable) :
    let := separableAdjoinRootDifferential f hsep
    DifferentialAlgebra K (AdjoinRoot f) := by
  dsimp
  let := separableAdjoinRootDifferential f hsep
  refine { deriv_algebraMap := ?_ }
  intro a
  change (Derivation.liftOfSurjective _ _) ((AdjoinRoot.mk f).toIntAlgHom (C a)) = _
  rw [Derivation.liftOfSurjective_apply, implicitDeriv_C]
  rfl

attribute [local instance] rationalDifferential

section
variable {F L : Type*} [Field F] [Field L] [Algebra F L] [Algebra (RatFunc F) L] [IsScalarTower F (RatFunc F) L]

lemma aeval_ratFunc_variable
    (a : F[X]) :
    aeval (algebraMap (RatFunc F) L RatFunc.X) a =
      algebraMap (RatFunc F) L (algebraMap F[X] (RatFunc F) a) := by
  induction a using Polynomial.induction_on' with
  | add a b ha hb => simp [map_add, ha, hb]
  | monomial n c =>
    simp [aeval_monomial, RatFunc.algebraMap_monomial, map_mul, map_pow,
      ← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply]

/-- In a differential algebra over `F(t)`, the constants of `F` have derivative zero. -/
lemma deriv_algebraMap_ratFunc_base
    [Differential L] [DifferentialAlgebra (RatFunc F) L] (a : F) :
    (algebraMap F L a)′ = 0 := by
  rw [IsScalarTower.algebraMap_apply F (RatFunc F) L, deriv_algebraMap]
  have ha : (algebraMap F (RatFunc F) a)′ = 0 := by
    change rationalDerivative (algebraMap F (RatFunc F) a) = 0
    rw [IsScalarTower.algebraMap_apply F F[X] (RatFunc F), rationalDerivative_polynomial]
    simp
  rw [ha, map_zero]

end

/-- In a differential algebra over `F(t)`, the image of `t` has derivative one. -/
lemma deriv_algebraMap_ratFunc_X {F L : Type*} [Field F] [Field L]
    [Algebra (RatFunc F) L] [Differential L] [DifferentialAlgebra (RatFunc F) L] :
    (algebraMap (RatFunc F) L RatFunc.X)′ = 1 := by
  rw [deriv_algebraMap]
  have hX : (RatFunc.X : RatFunc F)′ = 1 := by
    change rationalDerivative RatFunc.X = 1
    rw [← RatFunc.algebraMap_X, rationalDerivative_polynomial, derivative_X, map_one]
  rw [hX, map_one]

/-- The closed-form equation persists over the rational function field. -/
lemma bivariate_closed_form_map_ratFunc {F : Type*} [Field F] (f g h : F[X][X])
    (hclosed : (bivariateCoefficientDerivative F) g * f -
        g * (bivariateCoefficientDerivative F) f = h.derivative * f - h * f.derivative) :
    Differential.mapCoeffs (g.map (algebraMap F[X] (RatFunc F))) *
        f.map (algebraMap F[X] (RatFunc F)) -
      g.map (algebraMap F[X] (RatFunc F)) *
        Differential.mapCoeffs (f.map (algebraMap F[X] (RatFunc F))) =
      (h.map (algebraMap F[X] (RatFunc F))).derivative * f.map (algebraMap F[X] (RatFunc F)) -
        h.map (algebraMap F[X] (RatFunc F)) * (f.map (algebraMap F[X] (RatFunc F))).derivative := by
  rw [← bivariateCoefficientDerivative_map, ← bivariateCoefficientDerivative_map]
  simpa using
    congrArg (Polynomial.map (algebraMap F[X] (RatFunc F))) hclosed

/-- At a simple root over `F(t)`, the residue of a closed form lies in `F`. This is
the constant-residue descent, with the characteristic bounded by the residue
eliminant's degree. -/
lemma closed_form_residue_mem_base {F L : Type*} [Field F] [IsAlgClosed F] [Field L]
    [Algebra F L] [Algebra (RatFunc F) L] [IsScalarTower F (RatFunc F) L]
    [Differential L] [DifferentialAlgebra (RatFunc F) L]
    (f g h : F[X][X]) (hf : Irreducible (f.map (algebraMap F[X] (RatFunc F))))
    (hgdeg : g.natDegree < f.natDegree) (D : ℕ)
    (hfD : ∀ i, (f.coeff i).natDegree ≤ D) (hgD : ∀ i, (g.coeff i).natDegree ≤ D)
    (hchar : CharZeroOrGT L ((f.natDegree + (f.natDegree - 1)) * D))
    (hclosed : (bivariateCoefficientDerivative F) g * f -
        g * (bivariateCoefficientDerivative F) f = h.derivative * f - h * f.derivative)
    (β : L) (hβ : aeval β (f.map (algebraMap F[X] (RatFunc F))) = 0)
    (hs : aeval β (f.map (algebraMap F[X] (RatFunc F))).derivative ≠ 0) :
    aeval β (g.map (algebraMap F[X] (RatFunc F))) /
      aeval β (f.map (algebraMap F[X] (RatFunc F))).derivative ∈ (algebraMap F L).range := by
  let φ := algebraMap F[X] (RatFunc F)
  let ψ := algebraMap (RatFunc F) L
  let t : L := ψ RatFunc.X
  have hmaps (q : F[X][X]) : q.map (aeval t).toRingHom = (q.map φ).map ψ := by
    ext i
    simp
    exact aeval_ratFunc_variable _
  have hclosedL : Differential.mapCoeffs ((g.map φ).map ψ) * (f.map φ).map ψ -
      (g.map φ).map ψ * Differential.mapCoeffs ((f.map φ).map ψ) =
      ((h.map φ).map ψ).derivative * (f.map φ).map ψ -
        (h.map φ).map ψ * ((f.map φ).map ψ).derivative := by
    dsimp [ψ]
    simp [differential_mapCoeffs_map, derivative_map]
    simpa using
      congrArg (Polynomial.map (algebraMap (RatFunc F) L))
        (bivariate_closed_form_map_ratFunc f g h hclosed)
  have hrootL : ((f.map φ).map ψ).eval β = 0 := by aesop
  have hsL : ((f.map φ).map ψ).derivative.eval β ≠ 0 := by aesop
  have hder := closed_form_residue_deriv_eq_zero ((f.map φ).map ψ) ((g.map φ).map ψ)
    ((h.map φ).map ψ) β
    (by simp_all)
    (by simp_all) hclosedL
  by_cases hg : g = 0
  · simp [hg]
  have hh := differential_constant_mem_base_of_relation deriv_algebraMap_ratFunc_base t _
    deriv_algebraMap_ratFunc_X (by simp_all) (residueEliminant f g)
    (show residueEliminant f g ≠ 0 by
        let φ := algebraMap F[X] (RatFunc F)
        have hinj : Function.Injective φ := RatFunc.algebraMap_injective F
        have hg0 : (-g).map φ ≠ 0 := by
          intro h
          exact (neg_ne_zero.mpr hg)
            ((Polynomial.map_injective φ hinj) (h.trans (Polynomial.map_zero φ).symm))
        have hdegrees : ((-g).map φ).natDegree < (f.map φ).natDegree := by
          simpa [natDegree_map_eq_of_injective hinj, natDegree_neg] using hgdeg
        have hn : ((-g).map φ).natDegree ≤ f.natDegree - 1 := by
          rw [natDegree_map_eq_of_injective hinj, natDegree_neg]
          omega
        have hres : (f.map φ).resultant ((-g).map φ) (f.map φ).natDegree (f.natDegree - 1) ≠ 0 := by
          have hcop := hf.coprime_iff_not_dvd.mpr fun h =>
            (not_le_of_gt hdegrees) (natDegree_le_of_dvd h hg0)
          have he : (f.natDegree - 1) = ((-g).map φ).natDegree + ((f.natDegree - 1) - ((-g).map φ).natDegree) := by omega
          rw [he, resultant_add_right_deg _ _ _ _ _ le_rfl, coeff_natDegree]
          exact mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hf.ne_zero))
            (resultant_ne_zero (f.map φ) ((-g).map φ) hcop)
        intro h
        have hz := congrArg φ (congrArg residueParameterZero h)
        rw [map_zero, map_zero, residueEliminant_zero, ← resultant_map_map] at hz
        apply hres
        simpa [natDegree_map_eq_of_injective hinj] using hz)
    (hchar.mono (show (residueEliminant f g).natDegree ≤ (f.natDegree + (f.natDegree - 1)) * D by
        have hfl : ∀ i, ((f.map residueParameterLift).coeff i).natDegree ≤ D := by
          intro i
          simp
          exact natDegree_map_le.trans (hfD i)
        apply Polynomial.natDegree_resultant_le
        · exact hfl
        · intro i
          simp only [residueEliminationEquation, coeff_sub, coeff_C_mul]
          apply (natDegree_sub_le _ _).trans
          apply max_le
          · exact (natDegree_C_mul_le _ _).trans (coefficient_derivative_natDegree_le _ D hfl i)
          · simp
            exact natDegree_map_le.trans (hgD i)))
    (residueEliminant_eval_ratio_eq_zero t β f g hgdeg (by grind) (by grind))
  simpa only [hmaps, ψ, derivative_map, eval_map, aeval_def] using hh

variable {F : Type*} [Field F] [IsAlgClosed F] (f g h : F[X][X]) (hf : Irreducible f) (hm : f.Monic) (hgdeg : g.natDegree < f.natDegree) (hhdeg : h.natDegree < f.natDegree) (D : ℕ) (hfD : ∀ i, (f.coeff i).natDegree ≤ D) (hgD : ∀ i, (g.coeff i).natDegree ≤ D) (hmchar : CharZeroOrGT F f.natDegree) (hchar : CharZeroOrGT F ((f.natDegree + (f.natDegree - 1)) * D)) (hclosed : (bivariateCoefficientDerivative F) g * f - g * (bivariateCoefficientDerivative F) f = h.derivative * f - h * f.derivative)
include hf hm hgdeg hhdeg hfD hgD hmchar hchar hclosed

/-- The closed-form criterion over `F(t)`: a closed form within the degree bounds
is a constant multiple of the gradient. -/
lemma ratFunc_closed_form_eq_gradient
    :
    ∃ a : F,
      g.map (algebraMap F[X] (RatFunc F)) = C (algebraMap F (RatFunc F) a) *
        (f.map (algebraMap F[X] (RatFunc F))).derivative ∧
      h.map (algebraMap F[X] (RatFunc F)) = C (algebraMap F (RatFunc F) a) *
        Differential.mapCoeffs (f.map (algebraMap F[X] (RatFunc F))) := by
  let φ := algebraMap F[X] (RatFunc F)
  let fr := f.map φ
  have hinj := RatFunc.algebraMap_injective F
  have hfr : Irreducible fr := (hm.irreducible_iff_irreducible_map_fraction_map).mp hf
  have hfd := natDegree_map_eq_of_injective hinj f
  have hsep := (separable_iff_derivative_ne_zero hfr).mpr (derivative_ne_zero_of_natCast_natDegree_ne_zero
    ((hfd ▸ (hmchar.map (algebraMap F (RatFunc F)))) _ hfr.natDegree_pos le_rfl))
  let : Fact (Irreducible fr) := ⟨hfr⟩
  let : Fact fr.Monic := ⟨hm.map φ⟩
  let : Differential (AdjoinRoot fr) := separableAdjoinRootDifferential fr hsep
  have : DifferentialAlgebra (RatFunc F) (AdjoinRoot fr) :=
    separableAdjoinRootDifferential_algebra fr hsep
  let β : AdjoinRoot fr := AdjoinRoot.root fr
  have hβ : aeval β fr = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hs := hsep.aeval_derivative_ne_zero hβ
  have hres := closed_form_residue_mem_base f g h hfr hgdeg D hfD hgD
    (hchar.map (algebraMap F (AdjoinRoot fr))) hclosed β hβ hs
  have hdeg_lt (q : F[X][X]) (hq : q.natDegree < f.natDegree) : (q.map φ).degree < fr.degree := by
    rw [degree_eq_natDegree hfr.ne_zero]
    exact degree_le_natDegree.trans_lt
      (mod_cast (natDegree_map_eq_of_injective hinj q).trans_lt (hfd ▸ hq))
  exact closed_form_eq_constant_gradient_of_residue_mem_base fr (g.map φ) (h.map φ) hfr
    (hm.map φ) β hβ hs (hdeg_lt g hgdeg) (hdeg_lt h hhdeg)
    (bivariate_closed_form_map_ratFunc f g h hclosed) hres

/-- Over an algebraically closed field `F` of characteristic zero or larger than the
degree bounds, a monic irreducible bivariate equation has only constant-gradient closed
forms within the strict outer-variable degree bounds. -/
theorem bivariate_closed_form_eq_gradient
    :
    ∃ a : F, g = C (C a) * f.derivative ∧
      h = C (C a) * (bivariateCoefficientDerivative F) f := by
  let φ := algebraMap F[X] (RatFunc F)
  have hinj := RatFunc.algebraMap_injective F
  obtain ⟨a, ha, hb⟩ := ratFunc_closed_form_eq_gradient f g h hf hm hgdeg hhdeg D hfD hgD
    hmchar hchar hclosed
  refine ⟨a, Polynomial.map_injective φ hinj ?_, Polynomial.map_injective φ hinj ?_⟩
  · aesop
  · grind [Polynomial.map_mul, Polynomial.map_C, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C, bivariateCoefficientDerivative_map]

