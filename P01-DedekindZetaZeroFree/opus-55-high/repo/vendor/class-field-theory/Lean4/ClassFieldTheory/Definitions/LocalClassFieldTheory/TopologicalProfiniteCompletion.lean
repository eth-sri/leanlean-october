module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Topological profinite completion

This module defines the profinite completion of a topological group using its
open finite-index normal subgroups. The construction records the topology on
the source group, unlike the abstract profinite completion by all finite
quotients.
-/

noncomputable section

open CategoryTheory
open scoped Pointwise

namespace LocalClassFieldTheory

universe u

/-- An open normal subgroup whose quotient has finite cardinality. -/
def OpenFiniteIndexNormalSubgroup (G : Type u) [Group G] [TopologicalSpace G] :=
  { H : OpenNormalSubgroup G // H.toSubgroup.FiniteIndex }

namespace OpenFiniteIndexNormalSubgroup

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Open finite-index normal subgroups are ordered by inclusion. -/
instance : PartialOrder (OpenFiniteIndexNormalSubgroup G) :=
  Subtype.partialOrder
    (fun H : OpenNormalSubgroup G => H.toSubgroup.FiniteIndex)

/-- The inclusion preorder makes open finite-index normal subgroups a small thin category. -/
instance : SmallCategory (OpenFiniteIndexNormalSubgroup G) :=
  Preorder.smallCategory _
