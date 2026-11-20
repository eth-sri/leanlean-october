module

public import ValuedFieldTheory.LocalField.Analytic.DenominatorValuation
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.AdicPadicModule

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Principal-unit topology from a normalized valuation

For a complete discrete valuation with value group `WithZero (Multiplicative ℤ)`, the
inherited topology agrees with the canonical adic model, so the p-adic action and addition are
continuous on the original principal-unit carrier.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace CompleteDVF
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
namespace higherPrincipalUnitGroup

open LubinTate
open LubinTate.Valuations

variable {K : Type u} [Field K]

open Internal

variable (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)]

/-- Compare the type-level adic model with the principal-unit carrier under
the canonical topology of a normalized complete discrete valuation. -/
noncomputable def adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation :
    let F : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    AdicPrincipalUnits F.toCompleteDVF ≃ₜ+
      Additive
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1) := by
  let F := LocalField.ofWithZeroValuation v
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  letI : ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete
      (Valued.v : _root_.Valuation K
        (WithZero (Multiplicative ℤ))) := by
    infer_instance
  let π := chosenPrincipalUnitPadicUniformizer F.toCompleteDVF
  have hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K) :=
    chosenPrincipalUnitPadicUniformizer_isUniformizer F.toCompleteDVF
  have hadic :
      (inferInstance : TopologicalSpace F.toCompleteDVF.valuationSubring) =
        (LubinTate.Valuations.uniformizerPowerIdeal π 1).adicTopology := by
    have hmax :
        (inferInstance : TopologicalSpace F.toCompleteDVF.valuationSubring) =
          F.toCompleteDVF.maximalIdeal.adicTopology := by
      exact ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdic
        (K := K) (Gamma := WithZero (Multiplicative ℤ))
    have hideal : LubinTate.Valuations.uniformizerPowerIdeal π 1 =
        F.toCompleteDVF.maximalIdeal := by
      rw [LubinTate.Valuations.uniformizerPowerIdeal, pow_one,
        ← F.toCompleteDVF.maximalIdeal_eq_span_uniformizer hπ]
    simpa only [hideal] using hmax
  let Additive₀ := Additive ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1)
  let carrierTopology
      (t : TopologicalSpace F.toCompleteDVF.valuationSubring) :
      TopologicalSpace
        (Additive₀) :=
    letI : TopologicalSpace F.toCompleteDVF.valuationSubring := t
    inferInstance
  have hcarrier :
      (inferInstance : TopologicalSpace
        (Additive₀)) =
        principalUnitAdicTopology F.toCompleteDVF := by
    exact congrArg carrierTopology hadic
  have hcontinuous := Eq.mpr
      (congrArg
        (fun t : TopologicalSpace
            (Additive₀) =>
          @Continuous
            (AdicPrincipalUnits F.toCompleteDVF)
            (Additive₀)
            inferInstance t
            (AdicPrincipalUnits.equiv F.toCompleteDVF))
        hcarrier)
      continuous_induced_dom
  have hcontinuous_symm := Eq.mpr
      (congrArg
        (fun t : TopologicalSpace
            (Additive₀) =>
          @Continuous
            (Additive₀)
            (AdicPrincipalUnits F.toCompleteDVF)
            t inferInstance
            (AdicPrincipalUnits.equiv F.toCompleteDVF).symm)
        hcarrier)
      (continuous_induced_rng.2 (continuous_id_of_le le_rfl))
  exact ContinuousAddEquiv.mk'
    { toEquiv := AdicPrincipalUnits.equiv F.toCompleteDVF
      continuous_toFun := hcontinuous
      continuous_invFun := hcontinuous_symm }
    (fun _ _ => rfl)

/-- The same canonical action is jointly continuous for the topology carried
directly by a standard `ℤᵐ⁰`-valued complete discrete valuation.  The bridge
is the equality between the inherited valuation topology on the valuation
ring and its maximal-ideal adic topology. -/
theorem principalUnitPadicContinuousSMulOfWithZeroValuation :
    let F : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    ContinuousSMul ℤ_[F.residueCharacteristic]
      (Additive ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1)) := by
  let F := LocalField.ofWithZeroValuation v
  let := Valued.mk' v
  let e :=
    adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation v
  refine ⟨?_⟩
  exact e.continuous.comp (continuous_smul.comp (continuous_fst.prodMk (e.continuous_symm.comp continuous_snd)))

/-- Continuous addition on `Additive U^1` for the direct normalized
valuation topology. -/
theorem principalUnitPadicContinuousAddOfWithZeroValuation :
    let F : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    ContinuousAdd (Additive
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1)) := by
  let F := LocalField.ofWithZeroValuation v
  let := Valued.mk' v
  let e :=
    adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation v
  refine ⟨?_⟩
  exact e.continuous.comp (continuous_add.comp ((e.continuous_symm.comp continuous_fst).prodMk
    (e.continuous_symm.comp continuous_snd)))

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

end
