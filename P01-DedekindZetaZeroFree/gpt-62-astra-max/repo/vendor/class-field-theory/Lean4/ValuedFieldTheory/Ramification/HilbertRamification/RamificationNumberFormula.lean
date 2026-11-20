module

public import Mathlib.SetTheory.Cardinal.Finite
public import ValuedFieldTheory.Ramification.HilbertRamification.RamificationNumber
public import ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Herbrand-function sum formula for a general discretely valued field

This is the field-facing, noncomplete form of
the Herbrand-function sum formula.  The monogenic integral-generator theorem
supplies the generator hidden inside
`intrinsicRamificationNumberOfUniqueExtension`; the public endpoint therefore
uses exactly the canonical standing hypotheses and has no generator parameter.
-/

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
namespace Higher

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [FiniteDimensional K L] [base.valuation.HasExtension target.valuation]
variable [IsGalois K L]
variable [Algebra.IsSeparable base.residueField target.residueField]

local instance galoisFintype : Fintype Gal(L/K) :=
  Fintype.ofFinite Gal(L/K)

local instance subgroupFintype (H : Subgroup Gal(L/K)) : Fintype H :=
  Fintype.ofFinite H

local instance subgroupMembershipDecidable
    (H : Subgroup Gal(L/K)) (sigma : Gal(L/K)) : Decidable (sigma ∈ H) :=
  Classical.propDecidable _

end Higher
end RamificationTheory.HilbertRamification

end
