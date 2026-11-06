module

public import Mathlib.SetTheory.Cardinal.Finite
public import ValuedFieldTheory.LocalField.DiscreteValuationField.IwasawaPrincipalUnits
public import ValuedFieldTheory.LocalField.DiscreteValuationField.MixedCharacteristicStructure.Core

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Topological structure of local-field units

This file assembles the valuation, Teichmuller, and principal-unit factors in
the canonical factor order.  All topologies are the ones carried directly by
the given `WithZero (Multiplicative ℤ)`-valued valuation.
-/

noncomputable section

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace LocalField

variable {K : Type u} [Field K]



/-- The exact principal-unit factor in the equal-characteristic field-unit structure theorem, reindexed from
the prime-to-`p` degrees and residue-basis coordinates by `ℕ`. -/
noncomputable def chosenFirstPrincipalUnitStructure_equalCharacteristic
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)]
    [CharP K (ofWithZeroValuation v).residueCharacteristic] :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Multiplicative (ℕ → ℤ_[F.residueCharacteristic]) ≃ₜ*
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        F.toCompleteDVF 1 := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let hex := F.toCompleteDVF.exists_uniformizer
  let π := Classical.choose hex
  have hπ : v.IsUniformizer (π : K) := Classical.choose_spec hex
  let : ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete
      (Valued.v : _root_.Valuation K
        (WithZero (Multiplicative ℤ))) := by
    change ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v
    infer_instance
  let E :=
    (CompleteDVF.higherPrincipalUnitGroup.iwasawaGlobalAdicPrincipalUnitsContinuousAddEquiv
      F hπ).trans
      (CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation
        v)
  let I := iwasawaPadicIntProductContinuousAddEquivNat
    F.residueCharacteristic
    (CompleteDVF.higherPrincipalUnitGroup.iwasawaResidueRank F)
    F.residueCharacteristic_prime.pos
    Module.finrank_pos
  let eAdd : (ℕ → ℤ_[F.residueCharacteristic]) ≃ₜ+
      Additive
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          F.toCompleteDVF 1) :=
    I.symm.trans E
  exact LocalFieldTheory.DiscreteValuationField.continuousMulEquivOfAdditiveTarget eAdd



end LocalField
end LocalFieldTheory.DiscreteValuationField

end
