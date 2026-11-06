module

public import Mathlib

public import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.FixedFieldTower

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Hilbert ramification theory: number-field prime contractions

This file specializes the fixed fields `Z_P` and `T_P` to rings of integers
of number fields and defines the contracted primes `p`, `P_Z`, and `P_T`.
-/

noncomputable section

namespace HilbertRamification
namespace Dedekind

open Algebra NumberField
open scoped Pointwise

attribute [local instance] Ideal.Quotient.field

variable {K L : Type*}
variable [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable (G : Type*) [Group G] [MulSemiringAction G L] [SMulCommClass G K L]










/-- The contraction of a maximal finite prime of a number-field ring of
integers to a subfield ring of integers is nonzero. -/
def ringOfIntegers_under_ne_bot
    {E F : Type*} [Field E] [Field F] [NumberField E] [NumberField F]
    [Algebra E F] (P : Ideal (𝓞 F)) [P.IsMaximal]  := Ring.ne_bot_of_isMaximal_of_not_isField
      (M := P.under (𝓞 E)) inferInstance
      (RingOfIntegers.not_isField E)

/-- prime-decomposition theory:
`p = P ∩ O_K`, the prime ideal of the base number field below `P`. -/
abbrev basePrime
    (P : Ideal (𝓞 L))  :=
  P.under (𝓞 K)

/-- The contracted base prime is prime. -/
instance basePrime_isPrime
    (P : Ideal (𝓞 L)) [P.IsPrime] :
    (basePrime (K := K) P).IsPrime :=
  inferInstance































































































































end Dedekind
end HilbertRamification

end
