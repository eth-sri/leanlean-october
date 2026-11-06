module

public import Mathlib

public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestrictedTopology

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Multiplicative-range restriction for local fields

This file packages range restriction as a `LocalField` and exposes the
properness and completeness of the resulting topology.
-/

noncomputable section

universe u v

open scoped Valued

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace LocalField

variable {K : Type u} [Field K]














/-- The range-restricted topology attached to a local-field package is proper. -/
theorem mrangeRestrict_properSpace
    (F : LocalField.{u, v} K) :
    letI : Valued K
        (MonoidHom.mrange
          F.toCompleteDVF.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF)
    ProperSpace K := by
  apply LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_properSpace_of_residueField_finite

/-- The range-restricted topology attached to a local-field package is complete. -/
theorem mrangeRestrict_completeSpace
    (F : LocalField.{u, v} K) :
    letI : Valued K
        (MonoidHom.mrange
          F.toCompleteDVF.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF)
    CompleteSpace K := by
  apply LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_completeSpace_of_residueField_finite


end LocalField
end LocalFieldTheory.DiscreteValuationField

end
