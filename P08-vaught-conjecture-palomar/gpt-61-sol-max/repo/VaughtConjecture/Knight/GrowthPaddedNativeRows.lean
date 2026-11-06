/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GrowthPaddedCutTransport

/-! # Native higher-owner columns on the installed growth tower

The catalogue member at the owner's birth determines its entire padded table.
These are native row identities, not recognition assumptions or equalities
between independently selected renderings. The shadow maximum calculation
follows the grade-two calculation in V-C's GrowthLeafRecognition.
-/

namespace VaughtConjecture.Knight.GrowthPaddedNativeRows
open    Growth GrowthOrderedBase GrowthHigherSources
open GrowthPaddedContract GrowthPaddedIteration
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "build₀" => build I X T hA hB hC

/-- An actual leaf in its native build. -/
def owner : (t : ℕ) → (ht : t + 2 ≤ A.card) → Catalogue X (t + 2) →
    Cell (build₀ t ht).carrier
  | 0, _, a => GrowthPaddedSuccessor.leaf I X T hA hB hC a
  | t + 1, _, a => (GrowthPaddedStepRows.controller
      (build₀ t (by omega)) (by omega) a).1

def source : (t : ℕ) → (ht : t + 2 ≤ A.card) → Catalogue X (t + 2) →
    Cell (build₀ t ht).carrier → ExtOrd
  | 0, _, a => GrowthPaddedSuccessor.source I X T hA hB hC a
  | t + 1, _, a => GrowthPaddedStepRows.source
      (build₀ t (by omega)) (by omega) (by omega) a

def anchor : (t : ℕ) → (ht : t + 2 ≤ A.card) → Catalogue X (t + 2) → Catalogue X 1
  | 0, _, a => GrowthPaddedSuccessor.baseAnchor X a
  | t + 1, _, a => GrowthPaddedStepSupply.birth
      (build₀ t (by omega)) a

def ceiling t := CanonicalFieldLayer.ceiling (t + 2)
  (Field I.right.scheme I.left.scheme)

local notation "owner₀" => owner I X T hA hB hC

theorem owner_index t (ht : t + 2 ≤ A.card) a :
    (build₀ t ht).carrier.cell (owner₀ t ht a) =
      (A, t + 2) := by
  cases t with
  | zero => exact GrowthPaddedSuccessor.leaf_index a
  | succ t => exact (GrowthPaddedStepRows.controller _ _ a).2

local notation "source₀" => source I X T hA hB hC

theorem owner_row t (ht : t + 2 ≤ A.card) a
    d :
    (build₀ t ht).rows.E (owner₀ t ht a) d =
      source₀ t ht a d.1 := by
  cases t with
  | zero => exact GrowthPaddedSuccessor.leaf_row I X T hA hB hC a d
  | succ t => exact ScopedSourcePrefixLayer.Data.row_new _ _ d

local notation "anchor₀" => anchor I X T hA hB hC

theorem anchor_ranks t (ht : t + 2 ≤ A.card) a
    f :
    RelativeLadderLayer.ranks (fields X 1) (anchor₀ t ht a) f =
      LadderScalarRendering.fieldRank (fields X (t + 2) a) f := by
  cases t with
  | zero => exact GrowthPaddedSuccessor.baseAnchor_ranks X a f
  | succ t => exact GrowthPaddedStepSupply.birth_ranks _ a f

/-- The complete table, including unused ranks and every foreign shadow. -/
theorem source_base t (ht : t + 2 ≤ A.card) a
    d :
    source₀ t ht a ((build₀ t ht).baseMap d) =
      RelativeLadderLayer.renderWith I.boundary (by omega : 0 < A.card)
        (field I) (fields X 1) (anchor₀ t ht a)
        (fields X (t + 2) a) (ceiling I t) d := by
  cases t with
  | zero => exact LadderWeightedSuccessor.Input.source_old _ a d
  | succ t => exact GrowthPaddedStepSupply.source_base _ _ _ a d

theorem source_diagonal t (ht : t + 2 ≤ A.card) a :
    source₀ t ht a (owner₀ t ht a) =
      ceiling I t := by
  cases t with
  | zero => exact GrowthPaddedSuccessor.source_ceiling I X T hA hB hC a
  | succ t => exact ScopedSourcePrefixLayer.Data.profile_diagonal _ _

theorem source_original t (ht : t + 2 ≤ A.card) a
    d :
    source₀ t ht a ((build₀ t ht).baseMap
      (RelativeLadderLayer.old I.boundary (by omega : 0 < A.card) d)) =
        fields X (t + 2) a (field I d) := by simp_all [source_base, RelativeLadderLayer.renderWith_old, anchor_ranks]

abbrev ladder t (ht : t + 2 ≤ A.card)
    (v : RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme)
      (Q := Catalogue X 1)) :=
  (build I X T hA hB hC t ht).baseMap
    (RelativeLadderLayer.added I.boundary (by omega : 0 < A.card) v)

local notation "ladder₀" => ladder I X T hA hB hC

theorem ladder_index t (ht : t + 2 ≤ A.card)
    (v : RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme)
      (Q := Catalogue X 1)) :
    (build I X T hA hB hC t ht).carrier.cell (ladder₀ t ht v) = (A, 1) := by
  rw [ Layer.base_index, RelativeLadderLayer.added_index]

local notation "source₀₀" => source I X T hA hB hC

theorem source_ladder t (ht : t + 2 ≤ A.card) a
    (v : RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme)
      (Q := Catalogue X 1)) :
    source₀₀ t ht a (ladder₀ t ht v) =
      SupportLadderRows.image (RelativeLadderLayer.ranks (fields X 1))
        (anchor₀ t ht a)
        (LadderScalarRendering.level (LadderScalarRendering.values (fields X (t + 2) a))
          (ceiling I t)) v := by
  rw [ source_base]
  change RelativeLadderLayer.image _ _ _ _ _ _ (RelativeLadderLayer.added _ _ v) = _
  rw [RelativeLadderLayer.image, RelativeLadderLayer.rankIndex_added]
  rfl

/-- Complete fields, including hidden/future fields, are actual shadow maxima. -/
theorem source_shadow_sup t (ht : t + 2 ≤ A.card) a
    f :
    (Finset.univ : Finset (Catalogue X 1)).sup (fun b =>
      source₀₀ t ht a
        (ladder₀ t ht (SupportLadderRows.shadow b f))) =
          fields X (t + 2) a f := by
  
  have he := SupportLadderRows.readout_image
    
    (fun b f => le_of_lt (RelativeLadderLayer.rank_bound (fields X 1) b f))
    (anchor₀ t ht a)
    (LadderScalarRendering.level_mono (LadderScalarRendering.values_bound (anchor_bound X a))) f
  simp  [SupportLadderRows.readout] at he
  
  simp  [source_ladder]
  unfold ceiling
  rw [he, anchor_ranks, LadderScalarRendering.field_readback]

theorem source_spare t (ht : t + 2 ≤ A.card) a :
    source₀₀ t ht a (ladder₀ t ht
      (SupportLadderRows.leaf ( Nat.succ_pos _) (anchor₀ t ht a))) =
        ceiling I t := by
  rw [source_ladder, ]
  have he := SupportLadderRows.index_leaf (profile := RelativeLadderLayer.ranks (fields X 1))
    (show 0 < RelativeLadderLayer.rungs (X := Field I.right.scheme I.left.scheme)
      from Nat.succ_pos _) (anchor₀ t ht a) (anchor₀ t ht a)
  rw [FiniteProfileControllers.cut_refl] at he
  exact (congrArg (LadderScalarRendering.level
    (LadderScalarRendering.values (fields X (t + 2) a)) (ceiling I t)) he).trans (by
    
    apply ite_eq_left
    exact lt_of_le_of_lt (LadderScalarRendering.values_card_le (fields X (t + 2) a))
      (Nat.lt_succ_self _))

/-- Every earlier grade has a real ceiling occurrence in this native row.
The lower renderer is invoked with this row's fixed outer grid and ceiling. -/
theorem source_ceiling_at t (ht : t + 2 ≤ A.card) a
    i (hi : 1 ≤ i) (hit : i ≤ t + 2) :
    ∃ c ,
      (build₀ t ht).carrier.cell c = (A, i) ∧
        source₀ t ht a c = ceiling I t := by
  by_cases he : i = t + 2
  · subst i
    exact ⟨_, owner_index I X T hA hB hC t ht a, source_diagonal I X T hA hB hC t ht a⟩
  cases t with
  | zero =>
    have hie : i = 1 := by omega
    subst i
    exact ⟨_, ladder_index I X T hA hB hC 0 ht _, source_spare I X T hA hB hC 0 ht a⟩
  | succ t =>
    let P := build₀ t (by omega)
    obtain ⟨c, hc, hv⟩ := P.ceiling_at (Nat.le_succ (t + 2))
      (state X a) (state_admitted X) (state_proper X a)
       
      (fun _ hz => (PairedSlotComparison.sourceGrid_visible hz).mono (Nat.le_succ _))
      ((PairedSlotComparison.sourceGrid_visible
        (PairedSlotComparison.sourceGrid_endpoint le_rfl)).mono (Nat.le_succ _))
      (fun f => by rw [state_profile]; exact anchor_bound X a f) i hi (by omega)
    refine ⟨GrowthPaddedStepRows.old P (by omega) c,
      (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans hc, ?_⟩
    change GrowthPaddedStepRows.source P _ _ a (GrowthPaddedStepRows.old P _ c) = _
    rw [GrowthPaddedStepRows.source_old]
    exact hv

