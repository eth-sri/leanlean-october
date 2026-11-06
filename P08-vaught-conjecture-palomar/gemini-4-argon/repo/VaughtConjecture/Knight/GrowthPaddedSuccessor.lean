/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthHigherSources
public import VaughtConjecture.Knight.LadderWeightedSuccessor

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

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.GrowthPaddedSuccessor
open Transform Value ExtOrd Growth GrowthOrderedBase GrowthHigherSources SourcePrefixRows PairedSlotComparison

section Anchors
variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}
  (X : RelativeData DA semA DQ semQ)

def baseAnchor (a : Catalogue X 2) : Catalogue X 1 :=
  normalized X (by decide) (by decide : 1 ≤ 2)
    (state X a) (state_admitted X a) (state_proper X a)

theorem baseAnchor_ranks (a : Catalogue X 2) (d : Field DA DQ) :
    RelativeLadderLayer.ranks (fields X 1) (baseAnchor X a) d =
      LadderScalarRendering.fieldRank (fields X 2 a) d := by
  change LadderScalarRendering.fieldRank (fields X 1 (baseAnchor X a)) d = _
  rw [baseAnchor, normalized_fields, state_profile]
  exact ReceivingCatalogueRanks.fieldRank_normalize 1 a.val a.property.1.2 d

end Anchors

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

def input : LadderWeightedSuccessor.Input
    (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1) (U := Catalogue X 2) (V := Empty)
    I.boundary where
  sem := I.rows
  proper := proper I hB hC
  height := hA
  field := field I
  fields := fields X 1
  birth := GrowthOrderedBase.anchor_lawful I X T
  anchor := baseAnchor X
  upper := fields X 2
  rank_match := baseAnchor_ranks X
  incoming := anchor_lawful_at I X T
  visible := anchor_visible_one X
  grid := RecursiveRungRendering.grid (Field I.right.scheme I.left.scheme) 2
  bot_mem := sourceGrid_bot _ _
  ceiling := RecursiveRungRendering.ceiling (Field I.right.scheme I.left.scheme) 2
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hz := CanonicalFieldLayer.grid_bound _ _ hz
  grid_visible _ hz := sourceGrid_visible hz
  bounded := anchor_bound X
  nodeField v := Empty.elim v
  node_visible _ v := Empty.elim v

local notation "inp" => input I X T hA hB hC
open LadderWeightedSuccessor (Input)

abbrev carrier := Input.carrier inp
abbrev rows := Input.rows inp
abbrev source := Input.source inp
abbrev old := Input.old inp
abbrev leaf (a : Catalogue X 2) := Input.added inp (a, none)
abbrev original (d : Cell I.boundary) := old I X T hA hB hC
  (RelativeLadderLayer.old I.boundary (by omega : 0 < A.card) d)

theorem cell_cases (d : Cell (carrier I X T hA hB hC)) :
    (∃ x, d = old I X T hA hB hC x) ∨ ∃ a, d = leaf I X T hA hB hC a :=
  Input.cell_cases_empty inp d

theorem leaf_index (a : Catalogue X 2) :
    (carrier I X T hA hB hC).cell (leaf I X T hA hB hC a) = (A, 2) :=
  SourceLayerCarrier.cell_toCell _ _ _ _ _ _

theorem original_index (d : Cell I.boundary) :
    (carrier I X T hA hB hC).cell (original I X T hA hB hC d) =
      I.boundary.cell d := by
  rw [SourceLayerCarrier.cell_toCell]; exact RelativeLadderLayer.old_index _ _ d

theorem consistent : (rows I X T hA hB hC).IsConsistent := Input.consistent inp I.consistent

theorem source_lawful (a : Catalogue X 2) :
    RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2)
      (fun d => source I X T hA hB hC a d.1) := Input.source_lawful inp a

theorem inherited_row (c : Cell (Input.lower inp))
    (d : (Input.lower inp).below ((Input.lower inp).cell c)) :
    (rows I X T hA hB hC).E (old I X T hA hB hC c)
      (SeparatedSourceLayerCarrier.ownerEquiv (Input.lower inp)
        (Input.Node (U := Catalogue X 2) (V := Empty))
        2 (by decide) hA (Input.separation inp) c d) =
      (Input.lowerRows inp).E c d := Input.inherited_row inp c d

theorem original_readback (a : Catalogue X 2) (d : Cell I.boundary) :
    source I X T hA hB hC a (original I X T hA hB hC d) = fields X 2 a (field I d) :=
  Input.source_original inp a d

theorem source_ceiling (a : Catalogue X 2) :
    source I X T hA hB hC a (leaf I X T hA hB hC a) =
      RecursiveRungRendering.ceiling (Field I.right.scheme I.left.scheme) 2 :=
  Input.source_parent inp a

theorem source_prefix (a b : Catalogue X 2) {h : ExtOrd}
    (hh : h ∈ RecursiveRungRendering.grid (Field I.right.scheme I.left.scheme) 2)
    (hab : Agree (fields X 2 a) (fields X 2 b) h)
    (d : Cell (carrier I X T hA hB hC)) :
    min (source I X T hA hB hC a d) h = min (source I X T hA hB hC b d) h :=
  Input.source_prefix_all inp a b hh hab d

theorem source_supported (a : Catalogue X 2) (d : Cell (carrier I X T hA hB hC)) :
    OrbitPrefixSupport.Supported 2
      (RecursiveRungRendering.grid (Field I.right.scheme I.left.scheme) 2 : Set ExtOrd)
      (fields X 2 a) (source I X T hA hB hC a d) := Input.source_supported_all inp a d

theorem leaf_row (a : Catalogue X 2)
    (d : (carrier I X T hA hB hC).below
      ((carrier I X T hA hB hC).cell (leaf I X T hA hB hC a))) :
    (rows I X T hA hB hC).E (leaf I X T hA hB hC a) d =
      source I X T hA hB hC a d.1 := Input.leaf_row inp a d

theorem source_leaf (a b : Catalogue X 2) :
    source I X T hA hB hC a (leaf I X T hA hB hC b) =
      cut (RecursiveRungRendering.grid (Field I.right.scheme I.left.scheme) 2)
        (fields X 2 a) (fields X 2 b) := Input.source_leaf inp a b
