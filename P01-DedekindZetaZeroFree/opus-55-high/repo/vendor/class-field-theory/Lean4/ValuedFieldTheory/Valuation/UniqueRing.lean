module

public import ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Mathlib.FieldTheory.Normal.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


namespace ValuationTheory

/-!
# The unique-extension characterization: automorphism invariance from unique extension

The pullback of an extension valuation ring by a ground-field automorphism is
again an extension valuation ring.  Hence uniqueness forces the chosen ring
to be fixed by every automorphism of the extension field.  This is the first
Galois-theoretic step in the converse direction of the unique-extension characterization.
-/

noncomputable section

open scoped Pointwise

namespace Valuations

/-- The canonical homomorphism from the base valuation ring into an extension
valuation ring, without identifying either ring with the valuation subring of
its canonical valuation. -/
def valuationSubringMapOfHasExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    (hW : V.valuation.HasExtension W.valuation) : V →+* W := by
  letI : V.valuation.HasExtension W.valuation := hW
  exact (algebraMap K L).restrict V.toSubring W.toSubring (by
    intro x hx
    exact
      (ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_pullback_of_hasExtension_valuation
        V.valuation W x).2 (by
          simpa only [ValuationSubring.valuationSubring_valuation,
            ValuationSubring.mem_toSubring] using hx))
