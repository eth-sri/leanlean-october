/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GrowthPaddedNativeRows

/-! # Birth provenance for every inherited higher growth owner

The producer exhausts the actual installed inventory. Its returned maps preserve
occurrence order, every base coordinate, and the owner's entire native row.
No provenance or hidden-completion hypothesis is supplied by the caller.
-/

namespace VaughtConjecture.Knight.GrowthPaddedOwnerProvenance
open    Growth GrowthOrderedBase GrowthHigherSources
open GrowthPaddedContract GrowthPaddedIteration GrowthPaddedNativeRows
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "build₀" => build I X T hA hB hC

local notation "owner₀" => owner I X T hA hB hC

local notation "source₀" => source I X T hA hB hC

/-- Constructed birth data for an actual owner on a fixed final carrier. -/
structure Origin (t : ℕ) (ht : t + 2 ≤ A.card)
    (c : Cell (build₀ t ht).carrier) where
  birth : ℕ
  height : birth + 2 ≤ A.card
  member : Catalogue X (birth + 2)
  map : Cell (build₀ birth height).carrier →
    Cell (build₀ t ht).carrier
  index : ∀ d, (build₀ t ht).carrier.cell (map d) =
    (build₀ birth height).carrier.cell d
  base : ∀ d, map ((build₀ birth height).baseMap d) =
    (build₀ t ht).baseMap d
  occurrence : map (owner₀ birth height member) = c
  domain : (build₀ birth height).carrier.below
      ((build₀ birth height).carrier.cell
        (owner₀ birth height member)) ≃
    (build₀ t ht).carrier.below
      ((build₀ t ht).carrier.cell c)
  domain_val : ∀ d, (domain d).1 = map d.1
  row : ∀ d, (build₀ t ht).rows.E c (domain d) =
    source₀ birth height member d.1

local notation "Origin₀" => Origin I X T hA hB hC

def native t (ht : t + 2 ≤ A.card) a :
    Origin₀ t ht (owner₀ t ht a) where
  birth := t
  height := ht
  member := a
  map := id
  index _ := rfl
  base _ := rfl
  occurrence := rfl
  domain := Equiv.refl _
  domain_val _ := rfl
  row := owner_row I X T hA hB hC t ht a

def inherit (t : ℕ) (ht : (t + 1) + 2 ≤ A.card)
    (c : Cell (build₀ t (by omega)).carrier)
    (O : Origin₀ t (by omega) c) :
    Origin₀ (t + 1) ht
      (GrowthPaddedStepRows.old (build₀ t (by omega)) (by omega) c) where
  birth := O.birth
  height := O.height
  member := O.member
  map d := GrowthPaddedStepRows.old (build₀ t (by omega)) (by omega) (O.map d)
  index d := (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans (O.index d)
  base d := congrArg (GrowthPaddedStepRows.old _ _) (O.base d)
  occurrence := congrArg (GrowthPaddedStepRows.old _ _) O.occurrence
  domain := O.domain.trans (GrowthPaddedStepRows.ownerEquiv
    (build₀ t (by omega)) (by omega) (by omega) c)
  domain_val d := congrArg (GrowthPaddedStepRows.old _ _) (O.domain_val d)
  row d := (GrowthPaddedStepRows.inherited_row
    (build₀ t (by omega)) (by omega) (by omega) c (O.domain d)).trans (O.row d)

/-- Exhaustive actual-owner provenance, including every inherited layer. -/
theorem exists_origin (t : ℕ) (ht : t + 2 ≤ A.card)
    (c : Cell (build₀ t ht).carrier)
    (hc : (build₀ t ht).carrier.scope c = A)
    (hg : 2 ≤ (build₀ t ht).carrier.grade c) :
    Nonempty (Origin₀ t ht c) := by
  induction t with
  | zero =>
    rcases GrowthPaddedSuccessor.cell_cases c with ⟨d, rfl⟩ | ⟨a, rfl⟩
    · have hi : (build₀ 0 ht).carrier.cell
          (GrowthPaddedSuccessor.old I X T hA hB hC d) =
          (base I X T hA hB hC).cell d :=
        SourceLayerCarrier.cell_toCell _ _ _ _ _ _
      have hs  :=
        (congrArg Prod.fst hi).symm.trans hc
      have he := base_full_grade I X T hA hB hC d hs
      have hh : 2 ≤ (base I X T hA hB hC).grade d :=
        hg.trans_eq (congrArg Prod.snd hi)
      omega
    · solve_by_elim [native]
  | succ t ih =>
    let P := build₀ t (by omega)
    obtain ⟨x, hx⟩ := (SourceLayerCarrier.enumeration).surjective c
    
    rcases x with d | a
    · rw [← hx] at hc hg ⊢
      have hi : (build₀ (t + 1) ht).carrier.cell
          (SourceLayerCarrier.toCell P.carrier (Catalogue X (t + 2 + 1))
            (t + 2 + 1) (Nat.succ_pos _) (by omega) (.inl d)) = P.carrier.cell d :=
        SourceLayerCarrier.cell_toCell _ _ _ _ _ _
      obtain ⟨O⟩ := ih (by omega) d ((congrArg Prod.fst hi).symm.trans hc)
        (hg.trans_eq (congrArg Prod.snd hi))
      exact ⟨inherit I X T hA hB hC t ht d O⟩
    · rw [← hx]
      exact ⟨native I X T hA hB hC (t + 1) ht a⟩

variable {I X T hA hB hC} in
/-- Canonical chosen provenance, constructed from the actual inventory. -/
def origin {t : ℕ} {ht : t + 2 ≤ A.card}
    {c : Cell (build₀ t ht).carrier}
    (hc : (build₀ t ht).carrier.scope c = A)
    (hg : 2 ≤ (build₀ t ht).carrier.grade c) :=
  Classical.choice (exists_origin I X T hA hB hC t ht c hc hg)

namespace Origin
variable {I X T hA hB hC} {t : ℕ} {ht : t + 2 ≤ A.card}
  {c : Cell (build I X T hA hB hC t ht).carrier}
  (O : Origin I X T hA hB hC t ht c)

def owner_index :=
  (congrArg _ O.occurrence).symm.trans ((O.index _).trans
    (GrowthPaddedNativeRows.owner_index I X T hA hB hC O.birth O.height O.member))

def row_diagonal := by
  let e : (build₀ O.birth O.height).carrier.below
      ((build₀ O.birth O.height).carrier.cell
        (owner₀ O.birth O.height O.member)) :=
    ⟨owner₀ O.birth O.height O.member, GradedLe.refl _⟩
  have he : O.domain e = ⟨c, GradedLe.refl _⟩ :=
    Subtype.ext ((O.domain_val e).trans O.occurrence)
  exact (congrArg ((build₀ t ht).rows.E c) he).symm.trans
    ((O.row e).trans (source_diagonal I X T hA hB hC O.birth O.height O.member))

local notation "base₀" => GrowthPaddedContract.base I X T hA hB hC

/-- An actual base occurrence in this inherited owner's domain. -/
def baseArgument d
    (hd : GradedLe ((base₀).cell d) (A, O.birth + 2)) :
    (build₀ t ht).carrier.below
      ((build₀ t ht).carrier.cell c) :=
  ⟨(build₀ t ht).baseMap d, by rw [Layer.base_index, O.owner_index]; exact hd⟩

theorem row_base_source d
    (hd : GradedLe ((base₀).cell d) (A, O.birth + 2)) :
    (build₀ t ht).rows.E c (O.baseArgument d hd) =
      source₀ O.birth O.height O.member
        ((build₀ O.birth O.height).baseMap d) := by
  let e : (build₀ O.birth O.height).carrier.below
      ((build₀ O.birth O.height).carrier.cell
        (owner₀ O.birth O.height O.member)) :=
    ⟨(build₀ O.birth O.height).baseMap d, by
      rw [Layer.base_index, GrowthPaddedNativeRows.owner_index]; exact hd⟩
  have he : O.domain e = O.baseArgument d hd := Subtype.ext
    ((O.domain_val e).trans (O.base d))
  rw [← he, O.row]

local notation "fields₀" => fields X (O.birth + 2) O.member

/-- Present original fields are literal numerical columns. The membership
premise only asserts presence; absent future fields use the shadow theorem. -/
theorem row_original d
    (hd : GradedLe (I.boundary.cell d) (A, O.birth + 2)) :
    (build₀ t ht).rows.E c
      (O.baseArgument (RelativeLadderLayer.old I.boundary (by omega : 0 < A.card) d)
        (by simpa only [RelativeLadderLayer.old_index] using hd)) =
      fields₀ (field I d) := by
  rw [row_base_source, source_original]

def ladderArgument (v : RelativeLadderLayer.Point
    (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1)) :=
  O.baseArgument (RelativeLadderLayer.added I.boundary (by omega : 0 < A.card) v)
    (by rw [RelativeLadderLayer.added_index]; exact ⟨le_rfl, by omega⟩)

theorem row_ladder_source (v : RelativeLadderLayer.Point
    (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1)) :
    (build I X T hA hB hC t ht).rows.E c (O.ladderArgument v) =
      source₀ O.birth O.height O.member
        (ladder I X T hA hB hC O.birth O.height v) :=
  O.row_base_source _ _

/-- The full rank table, not merely represented-field readouts. -/
theorem row_ladder (v : RelativeLadderLayer.Point
    (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1)) :
    (build I X T hA hB hC t ht).rows.E c (O.ladderArgument v) =
      SupportLadderRows.image (RelativeLadderLayer.ranks (fields X 1))
        (anchor I X T hA hB hC O.birth O.height O.member)
        (LadderScalarRendering.level
          (LadderScalarRendering.values (fields₀))
          (ceiling I O.birth)) v := by
  rw [O.row_ladder_source, source_ladder]

theorem row_shadow_sup f :
    (Finset.univ : Finset (Catalogue X 1)).sup
      (fun b => (build₀ t ht).rows.E c
        (O.ladderArgument (SupportLadderRows.shadow b f))) =
      fields₀ f := by
  simp  [O.row_ladder_source]
  exact source_shadow_sup I X T hA hB hC O.birth O.height O.member f

theorem row_spare :
    (build₀ t ht).rows.E c
      (O.ladderArgument (SupportLadderRows.leaf ( Nat.succ_pos _)
        (anchor I X T hA hB hC O.birth O.height O.member))) = ceiling I O.birth := by
  rw [O.row_ladder_source]
  exact source_spare I X T hA hB hC O.birth O.height O.member

theorem row_ceiling_at i (hi : 1 ≤ i) (hib : i ≤ O.birth + 2) :
    ∃ d ,
      (build₀ t ht).carrier.cell d.1 = (A, i) ∧
        (build₀ t ht).rows.E c d = ceiling I O.birth := by
  obtain ⟨d, hd, hv⟩ := source_ceiling_at I X T hA hB hC O.birth O.height O.member i hi hib
  let e : (build₀ O.birth O.height).carrier.below
      ((build₀ O.birth O.height).carrier.cell
        (owner₀ O.birth O.height O.member)) :=
    ⟨d, by rw [hd, GrowthPaddedNativeRows.owner_index]; exact ⟨le_rfl, hib⟩⟩
  exact ⟨O.domain e, (congrArg _ (O.domain_val e)).trans ((O.index d).trans hd),
    (O.row e).trans hv⟩




