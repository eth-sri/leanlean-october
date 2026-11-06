module

public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Torsion
public import Mathlib.GroupTheory.FreeGroup.GeneratorEquiv
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Adjugate

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Witt's transfer theorem

For a finitely generated group `G` with finite abelianization, the transfer
from `G / G'` to `G' / G''` is trivial.

The proof follows Witt's group-ring argument. This file first
constructs the required right Fox coefficients directly from free words; no
presentation relations are assumed as extra input.
-/

open scoped BigOperators Pointwise

noncomputable section

namespace GroupTheory
namespace Transfer
namespace Witt


open Subgroup


variable {G : Type*} [Group G]

/-- Finite index of the commutator gives finiteness of the
abelianization. -/
instance finiteAbelianizationOfFiniteIndex
    [FiniteIndex (commutator G)] :
    Finite (Abelianization G) := by
  let : Fintype (Abelianization G) :=
    (commutator G).fintypeQuotientOfFiniteIndex
  exact Finite.of_fintype _
