module

public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsAbelianConductor
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.IntegerRingComparison
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.RamificationIndex
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.FiniteAbelian
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianConductorExactness
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Tame finite conductor exponents

For a finite abelian number-field extension, the conductor exponent at a
finite place is at most one exactly when the residue characteristic does not
divide the ideal-theoretic ramification index at any place above it.
-/

open scoped NumberField ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

end ClassFieldTheory

end
