module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFiniteTowerNormCore

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Ordinary norms in finite towers of rational fixed fields

This leaf compares the abstract relative norm in the rational idèle-class
direct limit with the ordinary idèle-class norm for a finite fixed-field
tower.  The upper field need not be Galois over the lower field.

The construction is kept separate from the foundational direct-limit norm
module so that the normal-closure and coset-product proof elaborates in a
fresh command environment.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology
open FiniteTowerNormCore

/-- The finite absolute quotient attached to a rational fixed field. -/
abbrev rationalFixedFieldAbsoluteQuotient
    (K : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :=
  (baseField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
    extensionSubgroup
      (baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
      K (le_baseField K)

/-- The finite relative quotient attached to an inclusion of rational
fixed fields. -/
abbrev rationalFixedFieldRelativeQuotient
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup) :=
  K.toSubgroup ⧸ extensionSubgroup K L hLK


















































































































end Reciprocity
end GlobalClassFieldTheory

end
