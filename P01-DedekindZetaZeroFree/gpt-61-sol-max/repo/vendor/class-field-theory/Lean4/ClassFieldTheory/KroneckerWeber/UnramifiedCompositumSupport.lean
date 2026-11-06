module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import ClassFieldTheory.AlgebraicNumberTheory.Ramification.RationalPrime
public import ClassFieldTheory.KroneckerWeber.Setup
public import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.CompositumUnramified

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Ramification support of the auxiliary compositum

Let `S` be the finite set of rational primes ramified in `L`, let
`n = ∏ p∈S, p ^ e_p`, and put `M = L(μ_n)`.  This file proves the
global ramification assertion used in the inertia count: every finite prime
of `M` outside `S` is unramified over `ℤ`.

The two factors are unramified outside `S` for different reasons.  For `L`
this is the definition of `S`; for the cyclotomic factor it is the standard
formula saying that a rational prime not dividing the conductor has
ramification index one.  An inertia automorphism of the compositum restricts
to inertia automorphisms of both factors.  Since the factors generate the
compositum, triviality of both restrictions implies triviality of the
original inertia automorphism.
-/

noncomputable section

namespace KroneckerWeber

open NumberField
open HilbertRamification.Dedekind
open AlgebraicNumberTheory.Ramification
open scoped NumberField

attribute [local instance] Ideal.Quotient.field

section ConductorSupport

variable (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L]
















end ConductorSupport

section FactorRamification

variable (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L]































































































end FactorRamification

section CompositumSupport

variable (L : Type) [Field L]
variable [hNF : NumberField L] [hLab : IsAbelianGalois ℚ L]

































































































end CompositumSupport

end KroneckerWeber

end
