module

public import Mathlib

public import ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairingSymbol

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Algebraic laws for Hilbert pairings
-/

namespace ClassFieldTheory.HilbertPairing

universe u

section
variable {K : Type u} [Field K] {n : ℕ+}
    (B : HilbertPairing K n)
include K n B
/-- The Steinberg relation for a pairing on power classes. -/
def IsSteinberg
       :=
  ∀ (a : Kˣ) (ha : 1 - (a : K) ≠ 0),
    B.symbol a (Units.mk0 (1 - (a : K)) ha) = 1

/-- Skew-symmetry of a pairing on power classes. -/
def IsSkewSymmetric
       :=
  ∀ a b : PowerClassGroup K n, B a b = (B b a)⁻¹

/-- Nondegeneracy in both variables of a pairing on power classes. -/
def IsNondegenerate
       :=
  (∀ a : PowerClassGroup K n,
      (∀ b : PowerClassGroup K n, B a b = 1) → a = 1) ∧
    (∀ b : PowerClassGroup K n,
      (∀ a : PowerClassGroup K n, B a b = 1) → b = 1)
end


end ClassFieldTheory.HilbertPairing
