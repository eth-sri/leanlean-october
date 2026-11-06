module

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
    (target : HenselianDVF.{w, x} L) : Prop :=
  ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.toDVF.valuation.HasExtension v'],
      target.toDVF.valuation.IsEquiv v'

omit [Algebra K L] in
/-- A Henselian-DVF valuation is equivalent to another valuation as soon as
their valuation subrings are equal. -/
theorem valuation_isEquiv_of_valuationSubring_eq
    (_base : HenselianDVF.{u, v} K) (target : HenselianDVF.{w, x} L)
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma')
    (hsub : target.toDVF.valuation.valuationSubring = v'.valuationSubring) :
    target.toDVF.valuation.IsEquiv v' :=
  (_root_.Valuation.isEquiv_iff_valuationSubring target.toDVF.valuation v').2 hsub

omit [Algebra K L] in
/-- Equivalent valuations have the same valuation subring. -/
theorem valuationSubring_eq_of_valuation_isEquiv
    (_base : HenselianDVF.{u, v} K) (target : HenselianDVF.{w, x} L)
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    {v' : _root_.Valuation L Gamma'}
    (h : target.toDVF.valuation.IsEquiv v') :
    target.toDVF.valuation.valuationSubring = v'.valuationSubring :=
  (_root_.Valuation.isEquiv_iff_valuationSubring target.toDVF.valuation v').1 h









/-- Henselian-DVF unique extension implies valuation-subring equality for every
extension valuation. -/
theorem valuationSubring_eq_of_hasUniqueValuationExtension
    (base : HenselianDVF.{u, v} K) (target : HenselianDVF.{w, x} L)
    (huniq : HasUniqueValuationExtension.{u, v, w, x, y} base target)
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.toDVF.valuation.HasExtension v'] :
    target.toDVF.valuation.valuationSubring = v'.valuationSubring :=
  valuationSubring_eq_of_valuation_isEquiv base target (@huniq Gamma' _ v' _)





end HenselianDVF
end DiscreteValuationField

end

end ValuationTheory
