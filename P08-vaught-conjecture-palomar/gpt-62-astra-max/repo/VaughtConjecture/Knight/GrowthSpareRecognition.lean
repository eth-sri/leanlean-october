/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFrame
public import VaughtConjecture.Knight.GrowthLeafRecognition
public import VaughtConjecture.Knight.GradePrefixProjection
public import VaughtConjecture.Knight.RelativeLadderAmbient

/-! # Grade-one recognition from the maximal spare chart, and the two-grade projection

`GrowthLeafRecognition` recognizes the **capped** vector `min (B_p f) (M₂ p)` from the maximal
leaf chart.  The mixed extension needs the **uncapped** shadow vector `B_p f` at grade one:
grade-one values above `M₂ p` must survive literally.  This module supplies it on the same
installed rows, again for an arbitrary lawful section `p` below `(A, 2)`, and combines the two
grades.

* **The base restriction** (`oldAt`, `base_lawful`): `p` restricted to the checked padded base
  below `(A, 1)` is lawful for the base rows (the inherited rows are literal, availability at
  grade one stays inside the base).
* **The maximal spare chart** (`exists_spare_chart`, from `RelativeLadderLayer.exists_leaf_chart`
  on the base): a spare rung attaining `M₁ p` whose chart `τ` through grade one reads every
  padded point **exactly** (uncapped) and every present grade-one original as the rank-coded
  source of its field.
* **Uncapped recognition** (`shadowSup_eq_spare`): `B_p f = τ (source rungs (rank_a f))` for every
  complete field, present, hidden or future; hence `present_readback_of_grade_one`.
* **Finite bottom reflection** (`spare_bottom_reflection`) on the rank-coded values when
  `M₁ p ≠ ⊥`, from `SupportLadderRows.bottom_reflection` on the ladder restriction.
* **Lawfulness and admission of `B_p` at grade one** (`private_uncapped_lawful`,
  `donor_uncapped_lawful`, `uncapped_visible`, `uncapped_shared`, `admitted_one`): the rank-coded
  original vectors are lawful (`RelativeLadderLayer.rank_respects`) and the chart transports them
  by finite reflection; admission at grade one additionally needs the activation grade to lie
  above one (`1 < X.req.N`, explicit: the correctness clause is not transported by a grade-one
  chart, and grade one is below activation in the intended regime).
* **The two-grade hidden-original projection** (`gradeHeight`, `private_projection_lawful`,
  `donor_projection_lawful`, `two_grade_projection`): the section `d ↦ min (B_p (field d))
  (H (grade d))` with `H 1 = ⊤` and `H 2 = M₂ p` is lawful below grade two on each original
  scheme (`GradePrefixProjection.respectsBelow`, antitone heights), and every present original
  reads it exactly: grade-one values uncapped, grade-two values at the leaf maximum.

Everything stays on the actual one-scope carrier; replication, mixed extension and lifting are not
touched. -/

@[expose] public section

namespace VaughtConjecture.Knight.GrowthSpareRecognition

open Transform Value ExtOrd Growth GrowthHigherSources GrowthLeafRecognition
open SupportLadderRows LadderScalarRendering SharpWitnessComposition CappedDonor.Ref

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : I.GrowthData}
  (frame : I.GrowthFrame X) (hA : 2 ≤ A.card)

local notation "Fld" => Field I.right.scheme I.left.scheme
local notation "ranks₁" => RelativeLadderLayer.ranks (fields X 1)
local notation "rungs" => RelativeLadderLayer.rungs (X := Fld)
local notation "spare" => SupportLadderRows.leaf (rungs_pos I)

/-! ## The base restriction of an arbitrary lawful section -/

/-! ## The maximal spare chart -/

variable (I X) in
/-- The ladder row of a spare at a padded point is the actual ladder row. -/
theorem ladderRow_spare_added a v :
    RelativeLadderLayer.ladderRow I.boundary (card_pos hA) (GrowthOrderedBase.field I) (fields X 1)
      (spare a) (RelativeLadderLayer.added I.boundary (card_pos hA) v) =
      SupportLadderRows.row ranks₁ (spare a) v := by
  change SupportLadderRows.source (SupportLadderRows.ceiling ranks₁ (spare a))
    (RelativeLadderLayer.rankIndex I.boundary (card_pos hA) (GrowthOrderedBase.field I)
      (fields X 1) (SupportLadderRows.parent (spare a))
      (RelativeLadderLayer.added I.boundary (card_pos hA) v)) = _
  rw [RelativeLadderLayer.rankIndex_added]
  rfl

variable (I X) in
/-- The ladder row of a spare at an original is the rank-coded source of its field. -/
theorem ladderRow_spare_old a d :
    RelativeLadderLayer.ladderRow I.boundary (card_pos hA) (GrowthOrderedBase.field I) (fields X 1)
      (spare a) (RelativeLadderLayer.old I.boundary (card_pos hA) d) =
      SupportLadderRows.source rungs (ranks₁ a (GrowthOrderedBase.field I d)) := by
  change SupportLadderRows.source (SupportLadderRows.ceiling ranks₁ (spare a))
    (RelativeLadderLayer.rankIndex I.boundary (card_pos hA) (GrowthOrderedBase.field I)
      (fields X 1) (SupportLadderRows.parent (spare a))
      (RelativeLadderLayer.old I.boundary (card_pos hA) d)) = _
  rw [RelativeLadderLayer.rankIndex_old, SupportLadderRows.ceiling_leaf]
  rfl

variable (I X) in
/-- The spare's row at a padded point is the rank-coded source at the point's index. -/
theorem row_spare a v :
    SupportLadderRows.row ranks₁ (spare a) v =
      SupportLadderRows.source rungs (SupportLadderRows.index ranks₁ a v) := by
  rw [SupportLadderRows.row, SupportLadderRows.ceiling_leaf]
  rfl

/-- Lawfulness below grade zero is vacuous: every cell has positive grade. -/
theorem respectsBelow_zero {ιS : Type*} [DecidableEq ιS] {S : Finset ιS} {DS : CellScheme S}
    semS (r : DS.SectionAt (S, 0)) :
    RespectsSemanticsBelow semS (S, 0) r := by
  have hno (d : DS.below (S, 0)) : False := by
    have h1 := d.2.2
    have h2 := DS.grade_pos d.1
    change DS.grade d.1 ≤ 0 at h1
    omega
  exact ⟨fun d => (hno d).elim, fun d => (hno d).elim, fun d => (hno d).elim⟩

end
end VaughtConjecture.Knight.GrowthSpareRecognition
