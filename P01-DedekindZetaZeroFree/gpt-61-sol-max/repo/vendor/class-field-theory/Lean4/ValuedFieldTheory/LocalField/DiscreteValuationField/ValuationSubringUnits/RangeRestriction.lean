module

public import Mathlib

public import ValuedFieldTheory.LocalField.DiscreteValuationField.Basic

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Restricting a valuation to its multiplicative range

The restricted valuation has the same valuation ring, maximal ideal, and
residue field as the original valuation.
-/

noncomputable section

universe u x

open WithZero
open scoped NNReal Valued WithZero

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace WithZeroValuation

variable {R : Type u}
variable {Gamma : Type x} [LinearOrderedCommGroupWithZero Gamma]

section Field

variable [Field R]

section
variable (v : _root_.Valuation R Gamma)
include v
/-- Restrict a valuation's codomain to its actual multiplicative range.

This removes irrelevant ambient value-group elements.  It is the value-group
normalization needed before finite-dimensional closedness can be used for an
abstract chosen local-field valuation. -/
def mrangeRestrict   :
    _root_.Valuation R (MonoidHom.mrange v.toMonoidWithZeroHom) where
  toFun r := ⟨v r, ⟨r, rfl⟩⟩
  map_one' := by
    ext
    exact map_one v
  map_zero' := by
    ext
    exact map_zero v
  map_mul' x y := by
    ext
    apply map_mul
  map_add_le_max' x y := by
    rw [← Subtype.coe_le_coe]
    exact map_add_le_max v x y

/-- The defining evaluation formula for `mrangeRestrict` is `(mrangeRestrict v x : Gamma) = v x`. -/
@[simp]
theorem mrangeRestrict_apply   (x : R) :
    (mrangeRestrict v x : Gamma) = v x :=
  rfl

/-- Passing to the actual multiplicative range does not change the valuation
subring predicate. -/
theorem mem_mrangeRestrict_valuationSubring_iff
      (x : R) :
    x ∈ (mrangeRestrict v).valuationSubring ↔ x ∈ v.valuationSubring := by
  rw [_root_.Valuation.mem_valuationSubring_iff,
    _root_.Valuation.mem_valuationSubring_iff]
  rw [← Subtype.coe_le_coe]
  rfl

/-- The valuation subring is unchanged after restricting the value group to
the actual multiplicative range. -/
noncomputable def valuationSubringEquivMrangeRestrict
      :
    v.valuationSubring ≃+* (mrangeRestrict v).valuationSubring where
  toFun x :=
    ⟨x, (mem_mrangeRestrict_valuationSubring_iff v x).2 x.2⟩
  invFun x :=
    ⟨x, (mem_mrangeRestrict_valuationSubring_iff v x).1 x.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  map_mul' x y := by ext; rfl
  map_add' x y := by ext; rfl

/--
Establishes the identity `((valuationSubringEquivMrangeRestrict v x : (mrangeRestrict
v).valuationSubring) : R) = x`.
-/
@[simp]
theorem valuationSubringEquivMrangeRestrict_apply_coe
      (x : v.valuationSubring) :
    ((valuationSubringEquivMrangeRestrict v x :
      (mrangeRestrict v).valuationSubring) : R) = x :=
  rfl
end


variable {K : Type u} [Field K]







































/-- Restricting a valuation to its actual multiplicative range induces the
same residue field. -/
noncomputable def residueFieldEquivMrangeRestrict
    (v : _root_.Valuation K Gamma) :
    IsLocalRing.ResidueField v.valuationSubring ≃+*
      IsLocalRing.ResidueField (mrangeRestrict v).valuationSubring := by
  let e := valuationSubringEquivMrangeRestrict v
  letI : IsLocalHom
      (e : v.valuationSubring →+* (mrangeRestrict v).valuationSubring) :=
    IsLocalHom.of_surjective
      (e : v.valuationSubring →+* (mrangeRestrict v).valuationSubring)
      e.surjective
  exact IsLocalRing.ResidueField.mapEquiv e

end Field

end WithZeroValuation
end LocalFieldTheory.DiscreteValuationField

end
