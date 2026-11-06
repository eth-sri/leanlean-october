/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GrowthHigherSources
import VaughtConjecture.Knight.LadderWeightedSuccessor

/-! # The installed second growth layer over the checked padded base

Specialize the existing weighted installer to ceiling leaves indexed by the
complete grade-two growth catalogue. Downward normalization supplies the
birth anchor, while the numerical source remains the original grade-two
vector. Original-owner lawfulness and whole-coordinate agreement are derived
from the actual boundary and rank renderer.

The construction follows the checked LOW initializer, without changing LOW,
the growth relation, or the padded base. This is consistency and selected
source lawfulness at one scope, not bountifulness or mixed-scope iteration.
-/

namespace VaughtConjecture.Knight.GrowthPaddedSuccessor
open    Growth GrowthOrderedBase GrowthHigherSources
open SourcePrefixRows PairedSlotComparison
noncomputable section

section
variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}
  (X : RelativeData DA semA DQ semQ)

def baseAnchor a :=
  normalized X (by decide) (by decide : 1 ≤ 2)
    (state X a) (state_admitted X) (state_proper X a)

theorem baseAnchor_fields a :
    fields X 1 (baseAnchor X a) = PairedSlotEncoding.normalize 1 (fields X 2 a) := by
  rw [baseAnchor, normalized_fields, state_profile]

theorem baseAnchor_ranks a d :
    RelativeLadderLayer.ranks (fields X 1) (baseAnchor X a) d =
      LadderScalarRendering.fieldRank (fields X 2 a) d := by
  change LadderScalarRendering.fieldRank (fields X 1 (baseAnchor X a)) d = _
  rw [baseAnchor_fields]
  exact ReceivingCatalogueRanks.fieldRank_normalize a.property.1.2

end

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "grid₀" => RecursiveRungRendering.grid (Field I.right.scheme I.left.scheme) 2

def input : LadderWeightedSuccessor.Input
    (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1) (U := Catalogue X 2) (V := Empty)
    I.boundary where
  sem := I.rows
  proper := proper hB hC
  height := hA
  field := field I
  fields := fields X 1
  birth := GrowthOrderedBase.anchor_lawful I X T
  anchor := baseAnchor X
  upper := fields X 2
  rank_match := baseAnchor_ranks X
  incoming := anchor_lawful_at I X T
  visible := anchor_visible_one X
  grid := grid₀
  bot_mem := sourceGrid_bot
  ceiling := RecursiveRungRendering.ceiling (Field I.right.scheme I.left.scheme) 2
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hz := CanonicalFieldLayer.grid_bound hz
  grid_visible _ hz := sourceGrid_visible hz
  bounded := anchor_bound X
  nodeField v := Empty.elim v
  node_visible _ v := Empty.elim v

local notation "input₀" => input I X T hA hB hC

abbrev carrier := (input₀).carrier
abbrev rows := (input₀).rows
abbrev source := (input₀).source
abbrev old := (input₀).old
abbrev leaf a := (input₀).added (a, none)
local notation "old₀" => old I X T hA hB hC

abbrev original d := old₀
  (RelativeLadderLayer.old I.boundary (by omega : 0 < A.card) d)

local notation "carrier₀" => carrier I X T hA hB hC

local notation "leaf₀" => leaf I X T hA hB hC

variable {I X T hA hB hC} in
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

variable {I X T hA hB hC} in
theorem leaf_index a :
    (carrier₀).cell (leaf₀ a) = (A, 2) :=
  SourceLayerCarrier.cell_toCell _ _ _ _ _ _

theorem original_index d :
    (carrier₀).cell (original I X T hA hB hC d) =
      I.boundary.cell d := by
  rw [SourceLayerCarrier.cell_toCell]
  exact RelativeLadderLayer.old_index d

local notation "rows₀" => rows I X T hA hB hC

theorem consistent : (rows₀).IsConsistent :=
  (input₀).consistent I.consistent

local notation "source₀" => source I X T hA hB hC

theorem source_lawful a :
    RespectsSemanticsBelow (rows₀) (A, 2)
      (fun d => source₀ a d.1) :=
  (input₀).source_lawful a

/-- Every retained rung, shadow, and proper original owner keeps its own row. -/
theorem inherited_row c
    d :
    (rows₀).E (old₀ c)
      (SeparatedSourceLayerCarrier.ownerEquiv (input₀).lower
        (LadderWeightedSuccessor.Input.Node (U := Catalogue X 2) (V := Empty))
        2 (by decide) hA (input₀).separation c d) =
      (input₀).lowerRows.E c d :=
  (input₀).inherited_row c d

theorem original_readback a d :
    source₀ a (original I X T hA hB hC d) =
      fields X 2 a (field I d) :=
  (input₀).source_original a d

theorem source_ceiling a :
    source₀ a (leaf₀ a) =
      RecursiveRungRendering.ceiling (Field I.right.scheme I.left.scheme) 2 :=
  (input₀).source_parent a

theorem source_prefix a b {h}
    (hh : h ∈ grid₀)
    (hab : Agree (fields X 2 a) (fields X 2 b) h)
    d :
    min (source₀ a d) h = min (source₀ b d) h :=
  (input₀).source_prefix_all a b hh hab d

variable {I X T hA hB hC} in
theorem source_supported a d :
    OrbitPrefixSupport.Supported 2
      (grid₀ : Set ExtOrd)
      (fields X 2 a) (source₀ a d) :=
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
        (fields X 2 a) (fields X 2 b) := by
  let J := input₀
  change WeightedSourcePrefixLayer.master J.data J.weight
    (J.controller (a, none)) (J.controller (b, none)).1 = _
  rw [WeightedSourcePrefixLayer.master_new]
  simp  [LadderWeightedSuccessor.Input.data,
    
    LadderWeightedSuccessor.Input.weight, ]
  exact min_eq_left (cut_le J.grid_bound)

