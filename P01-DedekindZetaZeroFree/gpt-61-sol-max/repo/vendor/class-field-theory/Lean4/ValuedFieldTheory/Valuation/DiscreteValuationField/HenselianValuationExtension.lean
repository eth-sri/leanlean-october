module

public import Mathlib

public import ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian
public import Mathlib.RingTheory.Valuation.Extension

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

namespace ValuationTheory

/-!
# Valuation-extension API for Henselian discretely valued fields

This file keeps the valuation-extension uniqueness interface separate from the
lightweight Henselian-DVF core.  The core file is used by Hensel lifting and
does not need to import mathlib's full `Valuation.HasExtension` API.
-/

noncomputable section

universe u v w x y

namespace DiscreteValuationField
namespace HenselianDVF

variable {K : Type u} [Field K]
variable {L : Type w} [Field L] [Algebra K L]

/-- A Henselian-DVF uniqueness predicate for extensions of the base valuation.
This is the non-complete analogue of the complete-DVF predicate used by
`ValuedExtension.HasUniqueValuationExtension`. -/
def HasUniqueValuationExtension (base : HenselianDVF.{u, v} K)
    (target : HenselianDVF.{w, x} L)  :=
  ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.toDVF.valuation.HasExtension v'],
      target.toDVF.valuation.IsEquiv v'

omit [Algebra K L] in
/-- A Henselian-DVF valuation is equivalent to another valuation as soon as
their valuation subrings are equal. -/
def valuation_isEquiv_of_valuationSubring_eq
    (_base : HenselianDVF.{u, v} K) (target : HenselianDVF.{w, x} L)
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma')
    (hsub : target.toDVF.valuation.valuationSubring = v'.valuationSubring)  :=
  (_root_.Valuation.isEquiv_iff_valuationSubring target.toDVF.valuation v').2 hsub








































































































end HenselianDVF
end DiscreteValuationField

end

end ValuationTheory
