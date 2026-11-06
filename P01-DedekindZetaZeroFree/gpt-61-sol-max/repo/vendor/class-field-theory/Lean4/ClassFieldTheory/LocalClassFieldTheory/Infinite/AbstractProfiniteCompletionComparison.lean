module

public import ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteCompletion

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

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

/-- The tautological equivalence between the discrete copy and the underlying type. -/
def equiv : AbstractProfiniteSource G ≃ G where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

/-- The discrete source copy inherits the group structure of `G`. -/
instance [Group G] : Group (AbstractProfiniteSource G) := (equiv G).group

/-- The abstract profinite source carries the discrete topology. -/
instance : TopologicalSpace (AbstractProfiniteSource G) := ⊥

/-- The topology on the abstract profinite source is discrete. -/
instance : DiscreteTopology (AbstractProfiniteSource G) := ⟨rfl⟩

/-- The discrete source copy of a group is a topological group. -/
instance [Group G] : IsTopologicalGroup (AbstractProfiniteSource G) := inferInstance






end AbstractProfiniteSource





















































































































section Comparison

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]







































































































































































end Comparison

end LocalClassFieldTheory

end
