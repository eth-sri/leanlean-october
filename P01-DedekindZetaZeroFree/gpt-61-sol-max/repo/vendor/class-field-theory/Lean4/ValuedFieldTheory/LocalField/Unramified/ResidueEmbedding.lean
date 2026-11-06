module

public import Mathlib

public import ValuedFieldTheory.LocalField.Unramified.MaximalSubextension
public import ValuedFieldTheory.LocalField.Unramified.BasicInvariants
public import Mathlib.FieldTheory.SeparableClosure

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Finite-subextension sources for residue embeddings

For the maximal unramified subextension `T`, the maximal-residue theorem identifies the
residue field with the separable closure of the base residue field and the
value group with that of the base.  This file proves the two corresponding
statements for every finite unramified subextension used to form `T`.

Passing these statements through the whole supremum requires closure under
finite composita (stability under finite composita); that missing step is not inserted here as an
extra hypothesis.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

section FiniteUnramifiedSubextensionInvariants

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

/-- Inclusion of the valuation ring of a restricted valuation into the
ambient valuation ring. -/
def restrictedValuationRingMapToAmbient
    (w : LubinTate.Valuations.ExponentialValuation L) (E : IntermediateField K L) :
    LubinTate.Valuations.exponentialValuationSubring
        (exponentialValuationRestrict w E) →+*
      LubinTate.Valuations.exponentialValuationSubring w :=
  E.val.toRingHom.restrict _ _ fun x hx ↦ by
    change (0 : WithTop ℝ) ≤ w x
    exact hx

@[simp]
theorem restrictedValuationRingMapToAmbient_apply
    (w : LubinTate.Valuations.ExponentialValuation L) (E : IntermediateField K L)
    (x : LubinTate.Valuations.exponentialValuationSubring
      (exponentialValuationRestrict w E)) :
    ((restrictedValuationRingMapToAmbient w E x) : L) = (x : E) :=
  rfl















































































































































































end FiniteUnramifiedSubextensionInvariants

end Valuations
end AlgebraicNumberTheory

end
