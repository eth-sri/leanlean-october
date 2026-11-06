module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFiniteTowerNormStatement

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Proof of ordinary norm comparison in finite towers of rational fixed fields

This proof leaf installs the canonical finite-tower context once and splits
the normal-closure embedding calculation, the pointwise coset action, and the
finite product calculation into separate commands.  The public theorem is a
thin wrapper around those providers.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology


section RationalFiniteTower

variable
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hKfinite : Finite (rationalFixedFieldAbsoluteQuotient K)]
    [hfinite : Finite
      (rationalFixedFieldRelativeQuotient K L hLK)]

local notation "F₀" =>
  abstractFixedField ℚ (SeparableClosure ℚ) K
local notation "E₀" =>
  abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
local notation "N₀" =>
  IntermediateField.normalClosure F₀ E₀ (SeparableClosure ℚ)
 abbrev rationalFiniteTowerRestrictedNormal :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  IntermediateField.restrictScalars ℚ N₀
 abbrev rationalFiniteTowerRestrictedUpper :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  IntermediateField.restrictScalars ℚ E₀
local notation "EQ₀" =>
  rationalFiniteTowerRestrictedUpper K L hLK
local notation "NQ₀" =>
  rationalFiniteTowerRestrictedNormal K L hLK
local notation "U₀" => rationalNormalClosure NQ₀
local notation "Q₀" =>
  K.toSubgroup ⧸ extensionSubgroup K L hLK
