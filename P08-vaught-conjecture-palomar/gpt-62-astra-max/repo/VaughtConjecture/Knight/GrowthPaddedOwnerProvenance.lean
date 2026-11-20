/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFrame
public import VaughtConjecture.Knight.GrowthPaddedNativeRows

/-! # Birth provenance for every inherited higher growth owner

The producer exhausts the actual installed inventory. Its returned maps preserve
occurrence order, every base coordinate, and the owner's entire native row.
No provenance or hidden-completion hypothesis is supplied by the caller.
-/
@[expose] public section

namespace VaughtConjecture.Knight.GrowthPaddedOwnerProvenance
open Transform Value ExtOrd Growth GrowthOrderedBase GrowthHigherSources
open GrowthPaddedContract GrowthPaddedIteration GrowthPaddedNativeRows
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : I.GrowthData}
  (frame : I.GrowthFrame X)

/-- Constructed birth data for an actual owner on a fixed final carrier. -/
structure Origin t (ht : t + 2 ≤ A.card)
    (c : Cell (build frame t ht).carrier) where
  birth : ℕ
  birth_le : birth ≤ t
  height : birth + 2 ≤ A.card
  member : Catalogue X (birth + 2)
  map : Cell (build frame birth height).carrier →
    Cell (build frame t ht).carrier
  order : StrictMono map
  index : ∀ d, (build frame t ht).carrier.cell (map d) =
    (build frame birth height).carrier.cell d
  base : ∀ d, map ((build frame birth height).baseMap d) =
    (build frame t ht).baseMap d
  occurrence : map (owner frame birth height member) = c
  domain : (build frame birth height).carrier.below
      ((build frame birth height).carrier.cell
        (owner frame birth height member)) ≃
    (build frame t ht).carrier.below
      ((build frame t ht).carrier.cell c)
  domain_val : ∀ d, (domain d).1 = map d.1
  row : ∀ d, (build frame t ht).rows.E c (domain d) =
    source frame birth height member d.1

def native t (ht : t + 2 ≤ A.card) a :
    Origin frame t ht (owner frame t ht a) where
  birth := t
  birth_le := le_rfl
  height := ht
  member := a
  map := id
  order := strictMono_id
  index _ := rfl
  base _ := rfl
  occurrence := rfl
  domain := Equiv.refl _
  domain_val _ := rfl
  row := owner_row frame t ht a

def inherit t (ht : (t + 1) + 2 ≤ A.card)
    (c : Cell (build frame t (by omega)).carrier)
    (O : Origin frame t (by omega) c) :
    Origin frame (t + 1) ht
      (PaddedTower.Step.old (build frame t (by omega)) (by omega) c) where
  birth := O.birth
  birth_le := O.birth_le.trans (Nat.le_succ t)
  height := O.height
  member := O.member
  map d := PaddedTower.Step.old (build frame t (by omega)) (by omega) (O.map d)
  order := (SourceLayerCarrier.old_order _ _ _ (Nat.succ_pos _) (by omega)).comp O.order
  index d := (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans (O.index d)
  base d := congrArg (PaddedTower.Step.old _ _) (O.base d)
  occurrence := congrArg (PaddedTower.Step.old _ _) O.occurrence
  domain := O.domain.trans (PaddedTower.Step.ownerEquiv
    (build frame t (by omega)) (by omega) (by omega) c)
  domain_val d := congrArg (PaddedTower.Step.old _ _) (O.domain_val d)
  row d := (PaddedTower.Step.inherited_row
    (build frame t (by omega)) (by omega) (by omega) c (O.domain d)).trans (O.row d)

/-- Exhaustive actual-owner provenance, including every inherited layer. -/
theorem exists_origin t (ht : t + 2 ≤ A.card)
    (c : Cell (build frame t ht).carrier)
    (hc : (build frame t ht).carrier.scope c = A)
    (hg : 2 ≤ (build frame t ht).carrier.grade c) :
    Nonempty (Origin frame t ht c) := by
  induction t with
  | zero =>
    let P := before frame 0 (by omega)
    obtain ⟨v, hv⟩ := (SourceLayerCarrier.enumeration P.carrier (Catalogue X 2) 2 (by decide) ht).surjective c
    change SourceLayerCarrier.toCell _ _ _ _ _ v = c at hv
    rw [← hv] at hc hg ⊢
    rcases v with d | a
    · have he := SourceLayerCarrier.cell_toCell P.carrier (Catalogue X 2) 2 (by decide) ht (.inl d)
      have h := (system frame).full_grade d ((congrArg Prod.fst he).symm.trans hc)
      exact False.elim ((by decide : ¬ 2 ≤ 1) ((hg.trans_eq (congrArg Prod.snd he)).trans_eq h))
    · exact ⟨native frame 0 ht a⟩
  | succ t ih =>
    let P := build frame t (by omega)
    obtain ⟨x, hx⟩ := (SourceLayerCarrier.enumeration P.carrier
      (Catalogue X (t + 2 + 1)) (t + 2 + 1) (Nat.succ_pos _) (by omega)).surjective c
    rcases x with d | a
    · rw [← hx] at hc hg ⊢
      have hi : (build frame (t + 1) ht).carrier.cell
          (SourceLayerCarrier.toCell P.carrier (Catalogue X (t + 2 + 1))
            (t + 2 + 1) (Nat.succ_pos _) (by omega) (.inl d)) = P.carrier.cell d :=
        SourceLayerCarrier.cell_toCell _ _ _ _ _ _
      obtain ⟨O⟩ := ih (by omega) d ((congrArg Prod.fst hi).symm.trans hc)
        (hg.trans_eq (congrArg Prod.snd hi))
      exact ⟨inherit frame t ht d O⟩
    · rw [← hx]
      exact ⟨native frame (t + 1) ht a⟩

/-- Canonical chosen provenance, constructed from the actual inventory. -/
def origin t (ht : t + 2 ≤ A.card)
    (c : Cell (build frame t ht).carrier)
    (hc : (build frame t ht).carrier.scope c = A)
    (hg : 2 ≤ (build frame t ht).carrier.grade c) :
    Origin frame t ht c :=
  Classical.choice (exists_origin frame t ht c hc hg)

namespace Origin
variable {frame} {t : ℕ} {ht : t + 2 ≤ A.card}
  {c : Cell (build frame t ht).carrier}
  (O : Origin frame t ht c)

theorem owner_index : (build frame t ht).carrier.cell c = (A, O.birth + 2) :=
  (congrArg _ O.occurrence).symm.trans ((O.index _).trans
    (GrowthPaddedNativeRows.owner_index frame O.birth O.height O.member))

theorem row_diagonal :
    (build frame t ht).rows.E c ⟨c, GradedLe.refl _⟩ =
      ceiling I O.birth := by
  let e : (build frame O.birth O.height).carrier.below
      ((build frame O.birth O.height).carrier.cell
        (owner frame O.birth O.height O.member)) :=
    ⟨owner frame O.birth O.height O.member, GradedLe.refl _⟩
  have he : O.domain e = ⟨c, GradedLe.refl _⟩ :=
    Subtype.ext ((O.domain_val e).trans O.occurrence)
  exact (congrArg ((build frame t ht).rows.E c) he).symm.trans
    ((O.row e).trans (source_diagonal frame O.birth O.height O.member))

/-- An actual base occurrence in this inherited owner's domain. -/
def baseArgument (d : Cell (GrowthPaddedContract.base frame))
    (hd : GradedLe ((GrowthPaddedContract.base frame).cell d) (A, O.birth + 2)) :
    (build frame t ht).carrier.below
      ((build frame t ht).carrier.cell c) :=
  ⟨(build frame t ht).baseMap d, by rw [PaddedTower.Layer.base_index, O.owner_index]; exact hd⟩

theorem row_base_source (d : Cell (GrowthPaddedContract.base frame))
    (hd : GradedLe ((GrowthPaddedContract.base frame).cell d) (A, O.birth + 2)) :
    (build frame t ht).rows.E c (O.baseArgument d hd) =
      source frame O.birth O.height O.member
        ((build frame O.birth O.height).baseMap d) := by
  let e : (build frame O.birth O.height).carrier.below
      ((build frame O.birth O.height).carrier.cell
        (owner frame O.birth O.height O.member)) :=
    ⟨(build frame O.birth O.height).baseMap d, by
      rw [PaddedTower.Layer.base_index, GrowthPaddedNativeRows.owner_index]; exact hd⟩
  have he : O.domain e = O.baseArgument d hd := Subtype.ext
    ((O.domain_val e).trans (O.base d))
  rw [← he, O.row]

/-- Present original fields are literal numerical columns. The membership
premise only asserts presence; absent future fields use the shadow theorem. -/
theorem row_original d
    (hd : GradedLe (I.boundary.cell d) (A, O.birth + 2)) :
    (build frame t ht).rows.E c
      (O.baseArgument (RelativeLadderLayer.old I.boundary frame.positive d)
        (by simpa only [RelativeLadderLayer.old_index] using hd)) =
      fields X (O.birth + 2) O.member (field I d) := by
  rw [row_base_source, source_original]

def ladderArgument (v : RelativeLadderLayer.Point
    (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1)) :
    (build frame t ht).carrier.below
      ((build frame t ht).carrier.cell c) :=
  O.baseArgument (RelativeLadderLayer.added I.boundary frame.positive v)
    (by rw [RelativeLadderLayer.added_index]; exact ⟨le_rfl, by omega⟩)

theorem row_ladder_source (v : RelativeLadderLayer.Point
    ) :
    (build frame t ht).rows.E c (O.ladderArgument v) =
      source frame O.birth O.height O.member
        (ladder frame O.birth O.height v) :=
  O.row_base_source _ _

/-- The full rank table, not merely represented-field readouts. -/
theorem row_ladder (v : RelativeLadderLayer.Point
    ) :
    (build frame t ht).rows.E c (O.ladderArgument v) =
      SupportLadderRows.image (RelativeLadderLayer.ranks (fields X 1))
        (anchor frame O.birth O.height O.member)
        (LadderScalarRendering.level
          (LadderScalarRendering.values (fields X (O.birth + 2) O.member))
          (ceiling I O.birth)) v := by
  rw [O.row_ladder_source, source_ladder]

theorem row_shadow_sup f :
    Finset.univ.sup
      (fun b => (build frame t ht).rows.E c
        (O.ladderArgument (SupportLadderRows.shadow b f))) =
      fields X (O.birth + 2) O.member f := by
  simp [O.row_ladder_source]
  exact source_shadow_sup frame O.birth O.height O.member f

theorem row_spare :
    (build frame t ht).rows.E c
      (O.ladderArgument (SupportLadderRows.leaf (Nat.succ_pos _)
        (anchor frame O.birth O.height O.member))) = ceiling I O.birth := by
  rw [O.row_ladder_source]
  exact source_spare frame O.birth O.height O.member

theorem row_ceiling_at i (hi : 1 ≤ i) (hib : i ≤ O.birth + 2) :
    ∃ d : (build frame t ht).carrier.below
        ((build frame t ht).carrier.cell c),
      (build frame t ht).carrier.cell d.1 = (A, i) ∧
        (build frame t ht).rows.E c d = ceiling I O.birth := by
  obtain ⟨d, hd, hv⟩ := source_ceiling_at frame O.birth O.height O.member i hi hib
  let e : (build frame O.birth O.height).carrier.below
      ((build frame O.birth O.height).carrier.cell
        (owner frame O.birth O.height O.member)) :=
    ⟨d, by rw [hd, GrowthPaddedNativeRows.owner_index]; solve_by_elim⟩
  exact ⟨O.domain e, (congrArg _ (O.domain_val e)).trans ((O.index d).trans hd),
    (O.row e).trans hv⟩

end Origin


end
end VaughtConjecture.Knight.GrowthPaddedOwnerProvenance
