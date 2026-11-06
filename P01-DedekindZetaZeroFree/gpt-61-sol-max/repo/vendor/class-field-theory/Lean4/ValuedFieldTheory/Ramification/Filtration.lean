module

public import Mathlib

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Natural-ceiling subgroup filtrations

Generic order-theoretic infrastructure for extending a natural-number-indexed
subgroup filtration to the real line by the natural-number ceiling.
-/

noncomputable section

namespace RamificationTheory

section IntegerStepFiltration

variable {G : Type*} [Group G]

/-- Extend a subgroup filtration indexed by natural numbers to the real line
by taking the natural-number ceiling.  This is the ceiling-indexed step
filtration relevant to the principal-unit filtration. -/
def natCeilStepFiltration
    (F : ℕ → Subgroup G) (t : ℝ)  :=
  F ⌈t⌉₊


























































































end IntegerStepFiltration

end RamificationTheory

end
