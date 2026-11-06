module

public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.ZMod.Units
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.Padics.RingHoms

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Ray class groups of the rational numbers

This file computes ray class groups of the rational numbers. A positive integer
`m` determines a full narrow ray modulus: its finite part has exponent
`m.factorization p` at `p`, and its real place imposes positivity. The
positive generator of an ideal prime to this modulus gives the explicit
isomorphism with `(ZMod m)ˣ`.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

namespace RayClass

local instance rationalRingOfIntegersIsPrincipalIdealRing :
    IsPrincipalIdealRing (𝓞 ℚ) :=
  IsPrincipalIdealRing.of_surjective
    Rat.ringOfIntegersEquiv.symm
    Rat.ringOfIntegersEquiv.symm.surjective

local instance rationalNatGeneratorPrimeFact
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.natGenerator v)) :=
  ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩

local instance rationalPrimesEquivPrimeFact
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Fact
      (Nat.Prime
        ((Rat.HeightOneSpectrum.primesEquiv
          (R := 𝓞 ℚ) v : Nat.Primes) : ℕ)) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv
    (R := 𝓞 ℚ) v).property⟩

/-- The height-one prime of `𝓞 ℚ` associated with a natural prime. -/
abbrev rationalPrime (p : Nat.Primes) :
    HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p

@[simp]
theorem natGenerator_rationalPrime (p : Nat.Primes) :
    Rat.HeightOneSpectrum.natGenerator (rationalPrime p) = p := 
  congrArg Subtype.val
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply p)

/-! ### The local congruence condition over `ℚ` -/

/-- The rational-prime equivalence identifies the local prime value with
the natural prime generator. -/
@[simp]
theorem primesEquiv_val_eq_natGenerator
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((Rat.HeightOneSpectrum.primesEquiv
      (R := 𝓞 ℚ) v : Nat.Primes) : ℕ) =
      Rat.HeightOneSpectrum.natGenerator v :=
  rfl
