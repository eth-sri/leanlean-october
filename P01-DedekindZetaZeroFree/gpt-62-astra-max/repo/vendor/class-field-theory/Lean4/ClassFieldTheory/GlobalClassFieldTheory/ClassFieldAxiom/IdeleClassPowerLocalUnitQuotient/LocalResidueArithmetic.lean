module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.FinitePlaceCompletionInstances
public import ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitPowerIndexFormulas
public import ValuedFieldTheory.LocalField.Padic.PrincipalUnits
public import ValuedFieldTheory.Valuation.ValuedAdicComplete
public import Mathlib.NumberTheory.NumberField.ProductFormula

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Residue arithmetic for finite-place power indices

This file relates global ideal norms to the residue fields and ramification
invariants of the corresponding finite completions.
-/

open scoped NumberField Classical NNReal ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- The ideal norm is the cardinality of the residue field of the
corresponding adic completion. -/
theorem absNorm_eq_card_adicResidueField
    (v : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm v.asIdeal =
      Nat.card
        (Valued.ResidueField (v.adicCompletion K)) := by
  exact
    Nat.card_congr
      (ringOfIntegersQuotientEquivAdicResidueField
        v).toEquiv

section

variable {E : Type*} [Field E] (ν : Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete ν]
    [Finite (IsLocalRing.ResidueField ν.valuationSubring)] [CharZero E]

/-- The valuation-theoretic ramification index used by the local field
formula agrees with the extension ramification index. -/
theorem ramificationIndexOfWithZeroValuation_eq_extensionRamificationIndex
    (hν : Function.Surjective ν) :
    let F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
        ν
    letI :
        LocalFieldTheory.DiscreteValuationField.LocalField.MixedQPadicContext
          F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContext
        F
    LocalFieldTheory.DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation
        ν =
      ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
        (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF
          F.residueCharacteristic).toDVF
        F.toCompleteDVF.toDVF := by
  let F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
      ν
  let p := F.residueCharacteristic
  let :=
    LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContext
      F
  let : Fact p.Prime :=
    ⟨F.residueCharacteristic_prime⟩
  let base :=
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p
  let target := F.toCompleteDVF
  let :=
    (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).instCompleteDiscrete.isRankOneDiscrete
  let ϖ :=
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicIntEquivValuationSubring
      p p
  have hϖval :
      base.valuation ϖ =
        WithZero.exp (-1 : ℤ) := by
    dsimp [base, ϖ]
    exact LocalFieldTheory.Padic.padicDVR_valuation_p p
  have hϖ :
      base.valuation.IsUniformizer
        ϖ := by
    dsimp [base, ϖ] at hϖval ⊢
    exact
      LocalFieldTheory.DiscreteValuationField.WithZeroValuation.isUniformizer_of_valuation_eq_exp_neg_one
        (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p)
        ((LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicIntEquivValuationSubring
          p p :
            (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF
              p).valuationSubring) : ℚ_[p])
        hϖval
  obtain ⟨π, hπval⟩ :=
    LocalFieldTheory.DiscreteValuationField.WithZeroValuation.exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective
      ν hν
  obtain ⟨u, hu⟩ :=
    LocalFieldTheory.DiscreteValuationField.ValuedExtension.exists_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image
      base target hϖ (LocalFieldTheory.DiscreteValuationField.WithZeroValuation.isUniformizer_of_valuation_eq_exp_neg_one
        ν (π : E) hπval)
  have huval :
      ν ((u : target.valuationSubring) : E) = 1 := by
    change
      ν (algebraMap target.valuationSubring E
        (u : target.valuationSubring)) = 1
    exact
      (Valuation.Integers.isUnit_iff_valuation_eq_one
        (Valuation.integer.integers ν)
        ).mp
        u.isUnit
  have hfield :
      ((ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap
          base.toDVF target.toDVF ϖ :
            target.valuationSubring) : E) =
        ((u : target.valuationSubring) : E) *
          (π : E) ^
            ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
              base.toDVF target.toDVF :=
    congrArg Subtype.val hu
  have hval := congrArg ν hfield
  have hpval :
      ν (p : E) =
        WithZero.exp
          (-(ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
            base.toDVF target.toDVF : ℤ)) := by
    rw [ν.map_mul, ν.map_pow, huval, hπval,
      one_mul] at hval
    calc
      _ =
          WithZero.exp (-1 : ℤ) ^
            ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
              base.toDVF target.toDVF := by
        refine (congrArg ν ?_).symm.trans hval
        exact map_natCast _ _
      _ =
          WithZero.exp
            (ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
              base.toDVF target.toDVF •
                (-1 : ℤ)) :=
        (WithZero.exp_nsmul _ _).symm
      _ =
          WithZero.exp
            (-(ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
              base.toDVF target.toDVF : ℤ)) := by
        simp
  have hint :=
    WithZero.exp_injective ((LocalFieldTheory.DiscreteValuationField.LocalField.valuation_residueCharacteristic_eq_exp_neg_ramificationIndex
      ν).symm.trans
      (by
        assumption))
  exact_mod_cast neg_injective hint

/-- The cardinality of a mixed-characteristic local residue field is
`p` to the residue degree. -/
theorem card_localField_residueField_eq_pow_residueDegree :
    let F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
        ν
    letI :
        LocalFieldTheory.DiscreteValuationField.LocalField.MixedQPadicContext
          F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContext
        F
    Nat.card F.residueField =
      F.residueCharacteristic ^
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF
            F.residueCharacteristic).toDVF
          F.toCompleteDVF.toDVF := by
  let F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
      ν
  let p := F.residueCharacteristic
  let :=
    LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContext
      F
  let base :=
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p
  let target := F.toCompleteDVF
  let :=
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF_residueField_finite p
  change
    Nat.card target.residueField =
      p ^
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          base.toDVF target.toDVF
  have hfinrank :
      Module.finrank base.residueField target.residueField =
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          base.toDVF target.toDVF := by
    rw [
      ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree_eq_finrank_quotient
        base target]
    rfl
  calc
    Nat.card target.residueField =
        Nat.card base.residueField ^
          Module.finrank base.residueField target.residueField :=
      Module.natCard_eq_pow_finrank
    _ = p ^
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          base.toDVF target.toDVF := by
      rw [hfinrank,
        LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF_residueField_card]

/-- Degree over `ℚ_p` is ramification index times residue degree. -/
theorem finrank_qp_eq_ramificationIndex_mul_residueDegree
    (hν : Function.Surjective ν) :
    let F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
        ν
    letI :
        LocalFieldTheory.DiscreteValuationField.LocalField.MixedQPadicContext
          F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContext
        F
    Module.finrank ℚ_[F.residueCharacteristic] E =
      LocalFieldTheory.DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation
          ν *
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF
            F.residueCharacteristic).toDVF
          F.toCompleteDVF.toDVF := by
  let F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
      ν
  let :=
    LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContext
      F
  rw [
    ramificationIndexOfWithZeroValuation_eq_extensionRamificationIndex
      ν hν]
  exact
    LocalFieldTheory.DiscreteValuationField.ValuedExtension.degree_eq_ramificationIndex_mul_residueDegree_of_finite_separable
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF
        F.residueCharacteristic) F.toCompleteDVF

end

/-- The absolute norm of `v` is `p^f`, with `p` the residue
characteristic and `f` the local residue degree. -/
theorem absNorm_eq_residueCharacteristic_pow_residueDegree
    (v : HeightOneSpectrum (𝓞 K)) :
    let ν :
        Valuation
          (v.adicCompletion K)
          (WithZero (Multiplicative ℤ)) :=
      Valued.v
    let F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
        ν
    letI :
        LocalFieldTheory.DiscreteValuationField.LocalField.MixedQPadicContext
          F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContext
        F
    Ideal.absNorm v.asIdeal =
      F.residueCharacteristic ^
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF
            F.residueCharacteristic).toDVF
          F.toCompleteDVF.toDVF := by
  let ν :
      Valuation
        (v.adicCompletion K)
        (WithZero (Multiplicative ℤ)) :=
    Valued.v
  let F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
      ν
  let :=
    LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContext
      F
  rw [absNorm_eq_card_adicResidueField]
  change
    Nat.card F.residueField =
      F.residueCharacteristic ^
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF
            F.residueCharacteristic).toDVF
          F.toCompleteDVF.toDVF
  exact card_localField_residueField_eq_pow_residueDegree ν

end GlobalClassFieldTheory.ClassFieldAxiom

end
