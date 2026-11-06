module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicPrincipalProduct

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# The rational cyclotomic product formula in arithmetic normalization

The arithmetic norm-residue symbol sends an ordinary unramified
uniformizer to arithmetic Frobenius.  At the ramified prime of a
prime-power cyclotomic layer, a local unit `u` therefore acts by
`u⁻¹`.  This file records those two signs on the actual chosen local
Artin maps and proves the finite principal-idèle product formula in
that normalization.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

local instance (q : Nat.Primes) : Fact q.1.Prime :=
  ⟨q.2⟩

local instance (m : ℕ+) : NeZero (m : ℕ) :=
  ⟨m.ne_zero⟩

section ArbitraryCyclotomicLevel

































































































end ArbitraryCyclotomicLevel

/-- The arithmetic chosen finite-place character of a rational
principal idèle at the prime `q`. -/
noncomputable def
    rationalCyclotomicArithmeticPrincipalFinitePlaceCharacter
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) (q : Nat.Primes) :
    (ZMod (p.1 ^ k))ˣ :=
  (rationalCyclotomicPrincipalFinitePlaceCharacter p k x q)⁻¹

/-- Arithmetic and geometric finite-place characters differ exactly
by inversion. -/
@[simp]
theorem
    rationalCyclotomicArithmeticPrincipalFinitePlaceCharacter_eq_inv
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) (q : Nat.Primes) :
    rationalCyclotomicArithmeticPrincipalFinitePlaceCharacter
        p k x q =
      (rationalCyclotomicPrincipalFinitePlaceCharacter
        p k x q)⁻¹ := by
  rfl





































































local instance (p : Nat.Primes) (k : ℕ) :
    NumberField
      (KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  KummerTheory.rationalCyclotomicLevel_numberField
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩

local instance (p : Nat.Primes) (k : ℕ) :
    FiniteDimensional ℚ
      (KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩

local instance (p : Nat.Primes) (k : ℕ) :
    IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicLevelIsAbelianGalois
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩






































































































































































end Reciprocity
end GlobalClassFieldTheory

end
