module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicPrincipalIdele
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicCharacterRigidity

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Prime-power detection for the rational cyclotomic `ZHat`-Artin map

Prime-power reductions of the genuine cyclotomic character detect the
full rational cyclotomic automorphism.  Restricting that automorphism
through actual finite cyclotomic levels then detects every finite
coordinate of the rational cyclotomic `ZHat`-extension.
-/

open scoped Classical NumberField IsMulCommutative
open NumberField ClassFormation

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

local instance (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

variable (a : IdeleGroup ℚ)
    (h : ∀ (p : Nat.Primes) (k : ℕ), Units.map (PadicInt.toZModPow k).toMonoidHom (KummerTheory.rationalCyclotomicCharacterPrimeProduct (infiniteGlobalArtinMonoidHom ℚ KummerTheory.rationalCyclotomicField a) p) ^ 2 = 1)

include h in
/-- If all prime-power character reductions of the full cyclotomic
global Artin symbol have square one, then the corresponding Artin symbol
in the actual rational `ZHat`-extension has square one. -/
theorem
    rationalCyclotomicZHatGlobalArtin_sq_eq_one_of_character_reductions :
    rationalCyclotomicZHatGlobalArtin a ^ 2 = 1 := by
  let σ :=
    infiniteGlobalArtinMonoidHom
      ℚ KummerTheory.rationalCyclotomicField a
  rw [rationalCyclotomicZHatGlobalArtin_eq_fullRestriction]
  rw [← map_pow, (rationalCyclotomicAutomorphism_sq_eq_one_of_character_reductions
    σ h), map_one]
include h in
/-- Prime-power square-one identities force the rational cyclotomic
idele value itself to be trivial.  Torsion-freeness of `ZHat` removes
the residual order-two ambiguity. -/
theorem
    rationalCyclotomicZHatIdeleValue_eq_one_of_character_reductions :
    rationalCyclotomicZHatIdeleValue a = 1 := by
  have hValue :
      rationalCyclotomicZHatIdeleValue a ^ 2 = 1 := by
    rw [rationalCyclotomicZHatIdeleValue_apply,
      ← map_pow, (rationalCyclotomicZHatGlobalArtin_sq_eq_one_of_character_reductions
        a h), map_one]
  exact
    (pow_left_injective
      (M := Multiplicative ZHat)
      (n := 2) (by norm_num))
        (by simpa using hValue)

end Reciprocity
end GlobalClassFieldTheory

end
