/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Descriptive.BFTree
public import InfinitaryLogic.Descriptive.AnalyticTreeBoundedness
public import InfinitaryLogic.Descriptive.AnalyticClosure

@[expose] public section

universe u v

namespace FirstOrder.Language

open Descriptive KleeneBrouwer MeasureTheory

variable {L : Language.{u, v}} [L.IsRelational]

/-- **Uniform back-and-forth separation.**  If `A` is an analytic set of pairs of codes and no
pair in `A` is isomorphic, then one countable back-and-forth level separates every pair of `A`.
No countability of the relation symbols is assumed. -/
theorem exists_uniform_bfSeparation {A : Set (StructureSpace L × StructureSpace L)}
    (hA : AnalyticSet A) (hA_noniso : ∀ p ∈ A, ¬ (structureIsoSetoid L).r p.1 p.2) :
    ∃ α : Ordinal.{0}, α < Ordinal.omega 1 ∧ ∀ p ∈ A, ¬ CodeBFEquiv α p.1 p.2 := by
  have hwf : ∀ p ∈ A, WellFounded (extBelow (bfTree p.1 p.2)) := fun p hp ↦
    (wellFounded_extBelow_iff_not_hasInfiniteBranch _).mpr fun hb ↦
      hA_noniso p hp ((hasInfiniteBranch_bfTree_iff _ _).mp hb)
  obtain ⟨α, hα, hbound⟩ := analytic_tree_rank_bounded hA (fun p ↦ bfTree p.1 p.2)
    isClosed_setOf_mem_bfTree hwf
  refine ⟨α, hα, fun p hp h ↦ ?_⟩
  have := hwf p hp
  exact ((lt_treeHeight_bfTree_of_codeBFEquiv h).trans (hbound p hp)).false

end FirstOrder.Language
