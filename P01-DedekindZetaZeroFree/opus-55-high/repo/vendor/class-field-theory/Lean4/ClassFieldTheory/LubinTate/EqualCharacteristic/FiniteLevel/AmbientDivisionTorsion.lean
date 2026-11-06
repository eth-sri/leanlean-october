module

public import ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.AmbientBracketAction

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Ambient Lubin--Tate division groups

The kernel of the `n`-fold distinguished endomorphism in any ambient field is
stable under all truncated brackets.  Units of `κ⟦T⟧` therefore act on it by
actual additive automorphisms.  This is the version needed in the separable
closure, where the nonzero division points live.
-/


open scoped PowerSeries LaurentSeries

universe u v w

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- Every iterate of `e` commutes with every ambient bracket. -/
theorem equalCharacteristicLubinTateAmbientPiIterate_bracket
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (ι : F.residueField →+* A) (t : A)
    (i n : ℕ) (a : F.residueField⟦X⟧) (x : A) :
    equalCharacteristicLubinTateAmbientPiIterate F t i
        (equalCharacteristicLubinTateAmbientBracket F ι t n a x) =
      equalCharacteristicLubinTateAmbientBracket F ι t n a
        (equalCharacteristicLubinTateAmbientPiIterate F t i x) := by
  induction i generalizing x with
  | zero =>
      simp [equalCharacteristicLubinTateAmbientPiIterate_zero]
  | succ i ih =>
      rw [equalCharacteristicLubinTateAmbientPiIterate_succ,
        equalCharacteristicLubinTateAmbientPiEnd_bracket, ih,
        equalCharacteristicLubinTateAmbientPiIterate_succ]
