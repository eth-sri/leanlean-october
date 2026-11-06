module

public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.FieldSpine

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Representatives and comparison endpoints for rational finite-norm transport

This compiled leaf preserves the original public declarations while reusing
the shared fixed-field instance providers.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFormation
open CyclicCohomology

section RationalIdeleExtension

open Reciprocity
open LocalClassFieldTheory

local instance
    representativesIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  RationalFiniteNormTransferInternal.ideleClassGroupIsMulCommutative

local instance
    representativesIdeleClassSubgroupNormal
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  RationalFiniteNormTransferInternal.ideleClassSubgroupNormal N






/-- The ordinary extension representative attached to the same base idele
class. -/
noncomputable def rationalFiniteNormTransferOrdinaryExtensionRepresentative
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (_hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := hKfinite) K) :
    rationalFiniteNormTransferExtensionIdeleClass K L hLK := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI : FiniteDimensional ℚ F :=
    RationalFiniteNormTransferInternal.fixedFiniteDimensional K
  letI : FiniteDimensional F E :=
    RationalFiniteNormTransferInternal.relativeFiniteDimensional
      K L hLK
  letI : IsScalarTower ℚ F E :=
    RationalFiniteNormTransferInternal.relativeScalarTower
      K L hLK
  letI : FiniteDimensional ℚ E :=
    RationalFiniteNormTransferInternal.relativeAbsoluteFiniteDimensional
      K L hLK
  letI : NumberField F :=
    RationalFiniteNormTransferInternal.fixedNumberField K
  letI : NumberField E :=
    RationalFiniteNormTransferInternal.relativeNumberField
      K L hLK
  letI : IsGalois F E :=
    RationalFiniteNormTransferInternal.relativeIsGalois
      K L hLK _hnormal
  exact ideleClassExtension F E c




end RationalIdeleExtension

end IdealClassFieldTheory
end GlobalClassFieldTheory

end
