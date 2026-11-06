
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.LowOnlyOrderedSources
import VaughtConjecture.Knight.LadderWeightedSuccessor

/-! # The first LOW successor on the unchanged padded base

The birth catalogue is the existing grade-one LOW catalogue. The new layer
has exactly one ceiling leaf per grade-two admitted canonical profile: the
weighted installer is specialized to an empty weighted-node type. The actual
predecessor sections, lawfulness, and agreement are constructed from the
ordered original boundary and downward normalization, not assumed.

This is one installed higher layer with consistent rows. Neither iteration
nor unrestricted bountifulness of the output is claimed.
-/

namespace VaughtConjecture.Knight.LowOnlyPaddedSuccessor
open    CappedDonor LowOnly LowOnlyOrderedLadder
open SourcePrefixRows PairedSlotComparison
noncomputable section

section
variable {n K : ℕ} {P C : SemScheme n} (F : LowOnly.Family P C K)

/-- Downward normalization chooses an existing birth anchor; numerical source
values are not identified with that anchor's normalized values. -/
def baseAnchor (a : F.Anchor 2) : F.Anchor 1 := by
  refine ⟨PairedSlotEncoding.normalize 1 a.val, ?_⟩
  obtain ⟨S, hS, he⟩ := a.property.2
  have hp : AvoidsValue S.profile ⊤ := by rw [he]; exact a.property.1.2
  have h := (LowOnlyRecursiveCoverage.normalizedAnchor F (by decide : 1 ≤ 1)
    (by decide : 1 ≤ 2) hS hp).property
  change F.fields 1 (LowOnlyRecursiveCoverage.normalizedAnchor F
    (by decide : 1 ≤ 1) (by decide : 1 ≤ 2) hS hp) ∈ F.catalogue 1 at h
  rw [LowOnlyRecursiveCoverage.normalizedAnchor_fields] at h
  simpa only [he] using h

theorem baseAnchor_ranks a d :
    RelativeLadderLayer.ranks (F.fields 1) (baseAnchor F a) d =
      LadderScalarRendering.fieldRank (F.fields 2 a) d :=
  ReceivingCatalogueRanks.fieldRank_normalize a.property.1.2

end

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : F.root.Covers I.shared.f I.shared.g)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "grid₀" => RecursiveRungRendering.grid (Field I.left I.right) 2

def input : LadderWeightedSuccessor.Input
    (X := Field I.left I.right) (Q := F.Anchor 1) (U := F.Anchor 2) (V := Empty)
    I.boundary where
  sem := I.rows
  proper := proper hB hC
  height := hA
  field := field I
  fields := F.fields 1
  birth := LowOnlyOrderedSources.anchor_lawful I F hroot 1
  anchor := baseAnchor F
  upper := F.fields 2
  rank_match := baseAnchor_ranks F
  incoming := LowOnlyOrderedSources.anchor_lawful I F hroot 2
  visible := LowOnlyRecursiveCharts.anchor_visible_one F (by decide)
  grid := grid₀
  bot_mem := sourceGrid_bot
  ceiling := RecursiveRungRendering.ceiling (Field I.left I.right) 2
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hz := CanonicalFieldLayer.grid_bound hz
  grid_visible _ hz := sourceGrid_visible hz
  bounded := LowOnlyRecursiveCharts.anchor_bound F
  nodeField v := Empty.elim v
  node_visible _ v := Empty.elim v

local notation "input₀" => input I F hroot hA hB hC

abbrev carrier := (input₀).carrier
abbrev rows := (input₀).rows
abbrev source := (input₀).source
abbrev old := (input₀).old
abbrev leaf a := (input₀).added (a, none)
local notation "old₀" => old I F hroot hA hB hC

abbrev original d := old₀
  (RelativeLadderLayer.old I.boundary (by omega : 0 < A.card) d)

local notation "carrier₀" => carrier I F hroot hA hB hC

local notation "leaf₀" => leaf I F hroot hA hB hC

variable {I F hroot hA hB hC} in
/-- Every new occurrence is a ceiling leaf, not a weighted node. -/
theorem cell_cases d :
    (∃ x, d = old₀ x) ∨
      ∃ a, d = leaf₀ a := by
  let J := input₀
  obtain ⟨x, hx⟩ := (SourceLayerCarrier.enumeration).surjective d
  change SourceLayerCarrier.toCell _ _ _ _ _ x = d at hx
  rcases x with x | ⟨a, v⟩
  · exact Or.inl ⟨x, hx.symm⟩
  · cases v with
    | none => exact Or.inr ⟨a, hx.symm⟩
    | some v => exact Empty.elim v

variable {I F hroot hA hB hC} in
theorem leaf_index a :
    (carrier₀).cell (leaf₀ a) = (A, 2) :=
  SourceLayerCarrier.cell_toCell _ _ _ _ _ _

theorem original_index d :
    (carrier₀).cell (original I F hroot hA hB hC d) =
      I.boundary.cell d := by
  rw [SourceLayerCarrier.cell_toCell]
  exact RelativeLadderLayer.old_index d

local notation "rows₀" => rows I F hroot hA hB hC

theorem consistent : (rows₀).IsConsistent :=
  (input₀).consistent I.consistent

local notation "source₀" => source I F hroot hA hB hC

theorem source_lawful a :
    RespectsSemanticsBelow (rows₀) (A, 2)
      (fun d => source₀ a d.1) :=
  (input₀).source_lawful a

/-- Every retained rung, shadow, and proper original owner keeps its own row. -/
theorem inherited_row c
    d :
    (rows₀).E (old₀ c)
      (SeparatedSourceLayerCarrier.ownerEquiv (input₀).lower
        (LadderWeightedSuccessor.Input.Node (U := F.Anchor 2) (V := Empty))
        2 (by decide) hA (input₀).separation c d) =
      (input₀).lowerRows.E c d :=
  (input₀).inherited_row c d

theorem original_readback a d :
    source₀ a (original I F hroot hA hB hC d) =
      F.fields 2 a (field I d) :=
  (input₀).source_original a d

theorem source_ceiling a :
    source₀ a (leaf₀ a) =
      RecursiveRungRendering.ceiling (Field I.left I.right) 2 :=
  (input₀).source_parent a

theorem source_prefix a b {h}
    (hh : h ∈ grid₀)
    (hab : Agree (F.fields 2 a) (F.fields 2 b) h)
    d :
    min (source₀ a d) h = min (source₀ b d) h :=
  (input₀).source_prefix_all a b hh hab d

variable {I F hroot hA hB hC} in
theorem source_supported a d :
    OrbitPrefixSupport.Supported 2
      (grid₀ : Set ExtOrd)
      (F.fields 2 a) (source₀ a d) :=
  (input₀).source_supported_all a d

/-- Each new row is the full selected source, with no residual weight cap. -/
theorem leaf_row a
    (d : (carrier₀).below
      ((carrier₀).cell (leaf₀ a))) :
    (rows₀).E (leaf₀ a) d =
      source₀ a d.1 := by
  let J := input₀
  have he := WeightedSourcePrefixLayer.row_new J.data J.weight J.weight_visible
    (J.controller (a, none)) d
  have hw : J.weight (J.controller (a, none)) = J.ceiling := by
    simp_all [VaughtConjecture.Knight.LadderWeightedSuccessor.Input.weight] <;> aesop
  exact he.trans ((congrArg (min (J.source a d.1)) hw).trans
    (min_eq_left (J.source_bound_all a d.1)))

theorem source_leaf a b :
    source₀ a (leaf₀ b) =
      cut (grid₀)
        (F.fields 2 a) (F.fields 2 b) := by
  let J := input₀
  change WeightedSourcePrefixLayer.master J.data J.weight
    (J.controller (a, none)) (J.controller (b, none)).1 = _
  rw [WeightedSourcePrefixLayer.master_new]
  simp  [LadderWeightedSuccessor.Input.data,
    
    LadderWeightedSuccessor.Input.weight, ]
  exact min_eq_left (cut_le J.grid_bound)

