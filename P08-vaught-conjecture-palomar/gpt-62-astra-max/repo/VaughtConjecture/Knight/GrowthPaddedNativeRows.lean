/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFrame
public import VaughtConjecture.Knight.GrowthPaddedIteration
public import VaughtConjecture.Knight.SeparatedLayerFace

/-! # Native higher-owner columns on the installed growth tower

The catalogue member at the owner's birth determines its entire padded table.
These are native row identities, not recognition assumptions or equalities
between independently selected renderings. The shadow maximum calculation
follows the grade-two calculation in V-C's GrowthLeafRecognition.
-/
@[expose] public section

namespace VaughtConjecture.Knight.GrowthPaddedNativeRows
open Transform Value ExtOrd Growth GrowthOrderedBase GrowthHigherSources
open GrowthPaddedContract GrowthPaddedIteration
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : I.GrowthData}
  (frame : I.GrowthFrame X)

/-- An actual leaf in its native build. -/
def owner (t : ℕ) (ht : t+2 ≤ A.card) (a : Catalogue X (t+2)) :=
  (PaddedTower.Step.controller (before frame t (by omega)) ht a).1

def source (t : ℕ) (ht : t+2 ≤ A.card) :=
  PaddedTower.Step.source (before frame t (by omega)) (Nat.succ_pos _) ht

def anchor (t : ℕ) (ht : t+2 ≤ A.card) := (before frame t (by omega)).birth

variable (I) in
def ceiling (t : ℕ) : ExtOrd := CanonicalFieldLayer.ceiling (t + 2)
  (Field I.right.scheme I.left.scheme)

theorem owner_index t (ht : t + 2 ≤ A.card) a :
    (build frame t ht).carrier.cell (owner frame t ht a) =
      (A, t + 2) :=
  (PaddedTower.Step.controller _ ht a).2

theorem owner_row t (ht : t + 2 ≤ A.card) a
    (d : (build frame t ht).carrier.below
      ((build frame t ht).carrier.cell (owner frame t ht a))) :
    (build frame t ht).rows.E (owner frame t ht a) d =
      source frame t ht a d.1 :=
  ScopedSourcePrefixLayer.Data.row_new _ _ d

theorem anchor_ranks t (ht : t + 2 ≤ A.card) a
    f :
    RelativeLadderLayer.ranks (fields X 1) (anchor frame t ht a) f =
      LadderScalarRendering.fieldRank (fields X (t + 2) a) f :=
  (before frame t (by omega)).birth_ranks a f

/-- The complete table, including unused ranks and every foreign shadow. -/
theorem source_base t (ht : t + 2 ≤ A.card) a
    (d : Cell (base frame)) :
    source frame t ht a ((build frame t ht).baseMap d) =
      RelativeLadderLayer.renderWith I.boundary frame.positive
        (field I) (fields X 1) (anchor frame t ht a)
        (fields X (t + 2) a) (ceiling I t) d :=
  PaddedTower.Step.source_base _ _ _ a d

theorem source_diagonal t (ht : t + 2 ≤ A.card) a :
    source frame t ht a (owner frame t ht a) =
      ceiling I t :=
  ScopedSourcePrefixLayer.Data.profile_diagonal _ _

theorem source_original t (ht : t + 2 ≤ A.card) a
    d :
    source frame t ht a ((build frame t ht).baseMap
      (RelativeLadderLayer.old I.boundary frame.positive d)) =
        fields X (t + 2) a (field I d) := by
  rw [source_base]
  exact RelativeLadderLayer.renderWith_old _ _ _ _ _ _ _ (anchor_ranks frame t ht a) d

abbrev ladder t (ht : t + 2 ≤ A.card)
    (v : RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme)
      (Q := Catalogue X 1)) :=
  (build frame t ht).baseMap
    (RelativeLadderLayer.added I.boundary frame.positive v)

theorem ladder_index t (ht : t + 2 ≤ A.card)
    (v : RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme)
      (Q := Catalogue X 1)) :
    (build frame t ht).carrier.cell (ladder frame t ht v) = (A, 1) := by
  rw [ladder, PaddedTower.Layer.base_index, RelativeLadderLayer.added_index]

theorem source_ladder t (ht : t + 2 ≤ A.card) a
    (v : RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme)
      (Q := Catalogue X 1)) :
    source frame t ht a (ladder frame t ht v) =
      SupportLadderRows.image (RelativeLadderLayer.ranks (fields X 1))
        (anchor frame t ht a)
        (LadderScalarRendering.level (LadderScalarRendering.values (fields X (t + 2) a))
          (ceiling I t)) v := by
  rw [ladder, source_base]
  change RelativeLadderLayer.image _ _ _ _ _ _ (RelativeLadderLayer.added _ _ v) = _
  rw [RelativeLadderLayer.image, RelativeLadderLayer.rankIndex_added]
  rfl

/-- Complete fields, including hidden/future fields, are actual shadow maxima. -/
theorem source_shadow_sup t (ht : t + 2 ≤ A.card) a
    f :
    (Finset.univ : Finset (Catalogue X 1)).sup (fun b =>
      source frame t ht a
        (ladder frame t ht (SupportLadderRows.shadow b f))) =
          fields X (t + 2) a f := by
  classical
  have he := SupportLadderRows.readout_image
    (H := RelativeLadderLayer.rungs (X := Field I.right.scheme I.left.scheme))
    (fun b f => le_of_lt (RelativeLadderLayer.rank_bound (fields X 1) b f))
    (anchor frame t ht a)
    (LadderScalarRendering.level_mono (LadderScalarRendering.values_bound (anchor_bound X a))) f
  simp only [SupportLadderRows.readout] at he
  rw [show Fintype.ofFinite (Catalogue X 1) = (inferInstance : Fintype (Catalogue X 1))
    from Subsingleton.elim _ _] at he
  simp only [source_ladder]
  unfold ceiling
  rw [he, anchor_ranks, LadderScalarRendering.field_readback]

theorem source_spare t (ht : t + 2 ≤ A.card) a :
    source frame t ht a (ladder frame t ht
      (SupportLadderRows.leaf (by exact Nat.succ_pos _) (anchor frame t ht a))) =
        ceiling I t := by
  rw [source_ladder, SupportLadderRows.image]
  have he := SupportLadderRows.index_leaf (profile := RelativeLadderLayer.ranks (fields X 1))
    (show 0 < RelativeLadderLayer.rungs (X := Field I.right.scheme I.left.scheme)
      from Nat.succ_pos _) (anchor frame t ht a) (anchor frame t ht a)
  rw [FiniteProfileControllers.cut_refl] at he
  exact (congrArg (LadderScalarRendering.level
    (LadderScalarRendering.values (fields X (t + 2) a)) (ceiling I t)) he).trans (by
    rw [LadderScalarRendering.level]
    apply ite_eq_left
    exact lt_of_le_of_lt (LadderScalarRendering.values_card_le (fields X (t + 2) a))
      (Nat.lt_succ_self _))

/-- Every earlier grade has a real ceiling occurrence in this native row.
The lower renderer is invoked with this row's fixed outer grid and ceiling. -/
theorem source_ceiling_at t (ht : t + 2 ≤ A.card) a
    i (hi : 1 ≤ i) (hit : i ≤ t + 2) :
    ∃ c : Cell (build frame t ht).carrier,
      (build frame t ht).carrier.cell c = (A, i) ∧
        source frame t ht a c = ceiling I t := by
  by_cases he : i = t + 2
  · subst i
    exact ⟨_, owner_index frame t ht a, source_diagonal frame t ht a⟩
  let P := before frame t (by omega)
  obtain ⟨c, hc, hv⟩ := P.ceiling_at a i hi (by omega)
  refine ⟨PaddedTower.Step.old P ht c, (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans hc, ?_⟩
  exact (PaddedTower.Step.source_old P _ ht a c).trans hv

end
end VaughtConjecture.Knight.GrowthPaddedNativeRows
