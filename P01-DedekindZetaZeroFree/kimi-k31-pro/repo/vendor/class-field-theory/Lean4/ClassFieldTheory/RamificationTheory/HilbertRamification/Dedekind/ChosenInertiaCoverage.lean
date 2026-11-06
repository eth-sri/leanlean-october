module

public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import ClassFieldTheory.AlgebraicNumberTheory.Ramification.RationalPrime
public import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Conjugation
public import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.NumberFieldPrimes

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/







set_option autoImplicit false

/-!
# Global cyclotomic inertia argument: coverage by finitely many chosen inertia groups

For an abelian Galois extension of `ℚ`, all primes above one rational prime
have the same inertia group: primes above the same rational prime are conjugate, and conjugation is
trivial in an abelian group.  Consequently, if the extension is unramified
outside a finite set `S`, one chosen prime above each member of `S` supplies
all nontrivial inertia groups.
-/

noncomputable section

namespace HilbertRamification.Dedekind

open NumberField
open scoped NumberField
open AlgebraicNumberTheory.Ramification

attribute [local instance] Ideal.Quotient.field



variable {G M : Type*}
variable [CommGroup G]
variable [Field M] [NumberField M]
variable [MulSemiringAction G M]
variable [IsGaloisGroup G ℚ M]



end HilbertRamification.Dedekind

end
