module

public import ValuedFieldTheory.Ramification.LocalField.Core
public import Mathlib.Tactic.NormNum

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Transport of upper ramification groups under an equivalent base field

The target field can carry two algebra structures whose base fields are
identified by a valuation-preserving field equivalence.  This file proves
that the resulting Galois groups have the same upper filtration, after
identifying their automorphisms by their common action on the target.
-/

noncomputable section

namespace RamificationTheory.LocalField

open LocalFieldTheory
open RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open scoped ValuativeRel

/-- If two base fields have the same image in a common extension, their
Galois groups are identified by leaving the underlying target automorphism
unchanged. -/
noncomputable def galoisGroupEquivOfBaseRingEquiv
    (B K E : Type)
    [Field B] [Field K] [Field E]
    [Algebra B E] [Algebra K E]
    (e : B ≃+* K)
    (he : ∀ b, algebraMap K E (e b) = algebraMap B E b) :
    Gal(E / B) ≃* Gal(E / K) where
  toFun σ :=
    { σ.toRingEquiv with
      commutes' := by
        intro k
        rw [← e.apply_symm_apply k, he]
        norm_num }
  invFun τ :=
    { τ.toRingEquiv with
      commutes' := by
        intro b
        rw [← he b]
        norm_num }
  left_inv σ := by
    grind
  right_inv τ := by
    grind
  map_mul' σ τ := by
    ext x
    rfl

@[simp]
theorem galoisGroupEquivOfBaseRingEquiv_apply
    (B K E : Type)
    [Field B] [Field K] [Field E]
    [Algebra B E] [Algebra K E]
    (e : B ≃+* K)
    (he : ∀ b, algebraMap K E (e b) = algebraMap B E b)
    (σ : Gal(E / B)) (x : E) :
    galoisGroupEquivOfBaseRingEquiv B K E e he σ x = σ x :=
  rfl





end RamificationTheory.LocalField

end
