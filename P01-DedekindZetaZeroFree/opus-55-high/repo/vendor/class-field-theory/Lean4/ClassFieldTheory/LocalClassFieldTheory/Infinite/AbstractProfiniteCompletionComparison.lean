module

public import ClassFieldTheory.Definitions.LocalClassFieldTheory.TopologicalProfiniteCompletion
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Comparison with the abstract profinite completion

The abstract profinite completion of a group is the completion formed from all
finite-index normal subgroups, without reference to a topology.  We realize it
by applying the open-quotient construction to a discrete copy of the group.

When every finite-index normal subgroup is open in the given topology, the
open-quotient completion and the abstract completion are canonically
isomorphic as topological groups.
-/

noncomputable section

open scoped Pointwise

namespace LocalClassFieldTheory

universe u v

/-- A copy of a group equipped with the discrete topology. -/
@[ext]
structure AbstractProfiniteSource (G : Type u) where
  /-- The underlying group element. -/
  val : G

namespace AbstractProfiniteSource

variable (G : Type u)

/-- The abstract profinite source carries the discrete topology. -/
instance : TopologicalSpace (AbstractProfiniteSource G) := ⊥

/-- The topology on the abstract profinite source is discrete. -/
instance : DiscreteTopology (AbstractProfiniteSource G) := ⟨rfl⟩
