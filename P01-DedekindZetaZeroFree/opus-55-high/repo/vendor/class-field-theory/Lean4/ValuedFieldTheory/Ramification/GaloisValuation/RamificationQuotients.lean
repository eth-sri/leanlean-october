module

public import Mathlib.GroupTheory.QuotientGroup.Finite

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Named quotients of antitone normal-subgroup filtrations

This module owns the opaque quotient carriers of a lower ramification
filtration and their construction, elimination, lifting, and mapping API.
Arithmetic Herbrand functions and valuation-action specializations live in
`RamificationTheory.GaloisValuation.Ramification`.
-/

noncomputable section

universe u v

namespace RamificationTheory
namespace DiscreteValuationField

/-- A generic antitone filtration by normal subgroups.  This interface contains
only the group-theoretic laws; arithmetic lower ramification filtrations are
canonical values constructed from valued extensions. -/
structure AntitoneNormalSubgroupFiltration (G : Type u) [Group G] where
  /-- The subgroup at each lower-filtration index. -/
  lower : ℕ → Subgroup G
  /-- Every subgroup in the lower filtration is normal. -/
  lower_normal : ∀ n : ℕ, (lower n).Normal
  /-- The lower filtration decreases as its index increases. -/
  antitone : ∀ {m n : ℕ}, m ≤ n → lower n ≤ lower m

namespace AntitoneNormalSubgroupFiltration

variable {G : Type u} [Group G] (F : AntitoneNormalSubgroupFiltration G)

/-- Provides the instance `lower_normal_instance`. -/
instance lower_normal_instance (n : ℕ) : (F.lower n).Normal :=
  F.lower_normal n
