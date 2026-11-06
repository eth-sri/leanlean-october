module

public import ValuedFieldTheory.LocalField.Unramified.Definitions

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# The maximal unramified subextension

Let `L/K` be an algebraic valued extension.  Its maximal unramified
subextension is the compositum, inside `L`, of all unramified subextensions.
Since the finite unramified-extension definition defines an arbitrary unramified extension as a union of
finite unramified subextensions, this compositum is the supremum of the finite
unramified intermediate fields.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

section MaximalUnramifiedSubextension

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

/-- The finite unramified intermediate fields occurring in the finite unramified-extension definition. -/
def finiteUnramifiedSubextensions
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) :
    Set (IntermediateField K L) :=
  {E | FiniteUnramifiedSubextension v w hExt E}

@[simp]
theorem mem_finiteUnramifiedSubextensions_iff
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    {E : IntermediateField K L} :
    E ∈ finiteUnramifiedSubextensions v w hExt ↔
      FiniteUnramifiedSubextension v w hExt E :=
  Iff.rfl

/-- The maximal unramified
subextension `T/K` of `L/K`.

The supremum is the field compositum.  Indexing by finite unramified
subextensions is literal the finite unramified-extension definition: every arbitrary unramified
subextension is their union. -/
def maximalUnramifiedSubextension
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) :
    IntermediateField K L :=
  sSup (finiteUnramifiedSubextensions v w hExt)







end MaximalUnramifiedSubextension

end Valuations
end AlgebraicNumberTheory

end
