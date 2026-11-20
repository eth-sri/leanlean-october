/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthLeafRecognition
public import VaughtConjecture.Knight.GradePrefixProjection
public import VaughtConjecture.Knight.RelativeLadderAmbient

@[expose] public section

namespace VaughtConjecture.Knight.GrowthSpareRecognition

open Transform Value ExtOrd Growth GrowthHigherSources GrowthPaddedSuccessor GrowthLeafRecognition

open SupportLadderRows LadderScalarRendering SharpWitnessComposition CappedDonor.Ref

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)} {m n J : ℕ} (I : WholeDonorBoundary.Input A B C R m (n + 1) J) (X : I.GrowthData) (hA : 2 ≤ A.card)

local notation "Fld" => Field I.right.scheme I.left.scheme

local notation "Pt" => RelativeLadderLayer.Point (X := Fld) (Q := Catalogue X 1)

local notation "ranks₁" => RelativeLadderLayer.ranks (fields X 1)

local notation "rungs" => RelativeLadderLayer.rungs (X := Fld)

local notation "spare" => SupportLadderRows.leaf (rungs_pos I)

/-- The ladder row of a spare at a padded point is the actual ladder row. -/
theorem ladderRow_spare_added (a : Catalogue X 1) (v : Pt) :
    RelativeLadderLayer.ladderRow I.boundary (card_pos hA) (GrowthOrderedBase.field I) (fields X 1)
      (spare a) (RelativeLadderLayer.added I.boundary (card_pos hA) v) =
      SupportLadderRows.row ranks₁ (spare a) v :=
  RelativeLadderLayer.ladderRow_added ..

/-- The ladder row of a spare at an original is the rank-coded source of its field. -/
theorem ladderRow_spare_old (a : Catalogue X 1) (d : Cell I.boundary) :
    RelativeLadderLayer.ladderRow I.boundary (card_pos hA) (GrowthOrderedBase.field I) (fields X 1)
      (spare a) (RelativeLadderLayer.old I.boundary (card_pos hA) d) =
      SupportLadderRows.source rungs (ranks₁ a (GrowthOrderedBase.field I d)) :=
  RelativeLadderLayer.ladderRow_old ..

/-- The spare's row at a padded point is the rank-coded source at the point's index. -/
theorem row_spare (a : Catalogue X 1) (v : Pt) :
    SupportLadderRows.row ranks₁ (spare a) v =
      SupportLadderRows.source rungs (SupportLadderRows.index ranks₁ a v) := rfl

/-- Lawfulness below grade zero is vacuous: every cell has positive grade. -/
theorem respectsBelow_zero {ιS : Type*} [DecidableEq ιS] {S : Finset ιS} {DS : CellScheme S}
    (semS : Semantics DS) (r : DS.below (S, 0) → ExtOrd) :
    RespectsSemanticsBelow semS (S, 0) r := by
  have hno (d : DS.below (S, 0)) : False := by
    have h1 := d.2.2
    have h2 := DS.grade_pos d.1
    aesop
  exact ⟨by tauto, by tauto, by tauto⟩

end

end VaughtConjecture.Knight.GrowthSpareRecognition
