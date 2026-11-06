/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

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
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

/-- Constructed birth data for an actual owner on a fixed final carrier. -/
structure Origin (t : ℕ) (ht : t + 2 ≤ A.card)
    (c : Cell (build I X T hA hB hC t ht).carrier) where
  birth : ℕ
  birth_le : birth ≤ t
  height : birth + 2 ≤ A.card
  member : Catalogue X (birth + 2)
  map : Cell (build I X T hA hB hC birth height).carrier →
    Cell (build I X T hA hB hC t ht).carrier
  order : StrictMono map
  index : ∀ d, (build I X T hA hB hC t ht).carrier.cell (map d) =
    (build I X T hA hB hC birth height).carrier.cell d
  base : ∀ d, map ((build I X T hA hB hC birth height).baseMap d) =
    (build I X T hA hB hC t ht).baseMap d
  occurrence : map (owner I X T hA hB hC birth height member) = c
  domain : (build I X T hA hB hC birth height).carrier.below
      ((build I X T hA hB hC birth height).carrier.cell
        (owner I X T hA hB hC birth height member)) ≃
    (build I X T hA hB hC t ht).carrier.below
      ((build I X T hA hB hC t ht).carrier.cell c)
  domain_val : ∀ d, (domain d).1 = map d.1
  row : ∀ d, (build I X T hA hB hC t ht).rows.E c (domain d) =
    source I X T hA hB hC birth height member d.1

section
variable (t : ℕ)

def native (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2)) :
    Origin I X T hA hB hC t ht (owner I X T hA hB hC t ht a) where
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
  row := owner_row I X T hA hB hC t ht a

def inherit (ht : (t + 1) + 2 ≤ A.card)
    (c : Cell (build I X T hA hB hC t (by omega)).carrier)
    (O : Origin I X T hA hB hC t (by omega) c) :
    Origin I X T hA hB hC (t + 1) ht
      (GrowthPaddedStepRows.old (build I X T hA hB hC t (by omega)) (by omega) c) where
  birth := O.birth
  birth_le := O.birth_le.trans (Nat.le_succ t)
  height := O.height
  member := O.member
  map d := GrowthPaddedStepRows.old (build I X T hA hB hC t (by omega)) (by omega) (O.map d)
  order := (SourceLayerCarrier.old_order _ _ _ (Nat.succ_pos _) (by omega)).comp O.order
  index d := (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans (O.index d)
  base d := congrArg (GrowthPaddedStepRows.old _ _) (O.base d)
  occurrence := congrArg (GrowthPaddedStepRows.old _ _) O.occurrence
  domain := O.domain.trans (GrowthPaddedStepRows.ownerEquiv
    (build I X T hA hB hC t (by omega)) (by omega) (by omega) c)
  domain_val d := congrArg (GrowthPaddedStepRows.old _ _) (O.domain_val d)
  row d := (GrowthPaddedStepRows.inherited_row
    (build I X T hA hB hC t (by omega)) (by omega) (by omega) c (O.domain d)).trans (O.row d)

section
variable (ht : t + 2 ≤ A.card) (c : Cell (build I X T hA hB hC t ht).carrier)

/-- Exhaustive actual-owner provenance, including every inherited layer. -/
theorem exists_origin (hc : (build I X T hA hB hC t ht).carrier.scope c = A)
    (hg : 2 ≤ (build I X T hA hB hC t ht).carrier.grade c) :
    Nonempty (Origin I X T hA hB hC t ht c) := by
  induction t with
  | zero =>
    rcases GrowthPaddedSuccessor.cell_cases I X T hA hB hC c with ⟨d, rfl⟩ | ⟨a, rfl⟩
    · have hi : (build I X T hA hB hC 0 ht).carrier.cell
          (GrowthPaddedSuccessor.old I X T hA hB hC d) =
          (base I X T hA hB hC).cell d :=
        SourceLayerCarrier.cell_toCell _ _ _ _ _ _
      have hs : (base I X T hA hB hC).scope d = A :=
        (congrArg Prod.fst hi).symm.trans hc
      have he := base_full_grade I X T hA hB hC d hs
      have hh : 2 ≤ (base I X T hA hB hC).grade d :=
        hg.trans_eq (congrArg Prod.snd hi)
      omega
    · exact ⟨native I X T hA hB hC 0 ht a⟩
  | succ t ih =>
    let P := build I X T hA hB hC t (by omega)
    obtain ⟨x, hx⟩ := (SourceLayerCarrier.enumeration P.carrier
      (Catalogue X (t + 2 + 1)) (t + 2 + 1) (Nat.succ_pos _) (by omega)).surjective c
    change SourceLayerCarrier.toCell _ _ _ _ _ x = c at hx
    rcases x with d | a
    · rw [← hx] at hc hg ⊢
      have hi : (build I X T hA hB hC (t + 1) ht).carrier.cell
          (SourceLayerCarrier.toCell P.carrier (Catalogue X (t + 2 + 1))
            (t + 2 + 1) (Nat.succ_pos _) (by omega) (.inl d)) = P.carrier.cell d :=
        SourceLayerCarrier.cell_toCell _ _ _ _ _ _
      obtain ⟨O⟩ := ih (by omega) d ((congrArg Prod.fst hi).symm.trans hc)
        (hg.trans_eq (congrArg Prod.snd hi))
      exact ⟨inherit I X T hA hB hC t ht d O⟩
    · rw [← hx]
      exact ⟨native I X T hA hB hC (t + 1) ht a⟩

/-- Canonical chosen provenance, constructed from the actual inventory. -/
def origin (hc : (build I X T hA hB hC t ht).carrier.scope c = A)
    (hg : 2 ≤ (build I X T hA hB hC t ht).carrier.grade c) :
    Origin I X T hA hB hC t ht c :=
  Classical.choice (exists_origin I X T hA hB hC t ht c hc hg)

end

end

namespace Origin
variable {I X T hA hB hC} {t : ℕ} {ht : t + 2 ≤ A.card}
  {c : Cell (build I X T hA hB hC t ht).carrier}
  (O : Origin I X T hA hB hC t ht c)

theorem owner_index : (build I X T hA hB hC t ht).carrier.cell c = (A, O.birth + 2) :=
  (congrArg _ O.occurrence).symm.trans ((O.index _).trans
    (GrowthPaddedNativeRows.owner_index I X T hA hB hC O.birth O.height O.member))

theorem row_diagonal :
    (build I X T hA hB hC t ht).rows.E c ⟨c, GradedLe.refl _⟩ =
      ceiling I O.birth := by
  let e : (build I X T hA hB hC O.birth O.height).carrier.below
      ((build I X T hA hB hC O.birth O.height).carrier.cell
        (owner I X T hA hB hC O.birth O.height O.member)) :=
    ⟨owner I X T hA hB hC O.birth O.height O.member, GradedLe.refl _⟩
  have he : O.domain e = ⟨c, GradedLe.refl _⟩ :=
    Subtype.ext ((O.domain_val e).trans O.occurrence)
  exact (congrArg ((build I X T hA hB hC t ht).rows.E c) he).symm.trans
    ((O.row e).trans (source_diagonal I X T hA hB hC O.birth O.height O.member))

section
variable (d : Cell (GrowthPaddedContract.base I X T hA hB hC)) (hd : GradedLe ((GrowthPaddedContract.base I X T hA hB hC).cell d) (A, O.birth + 2))

/-- An actual base occurrence in this inherited owner's domain. -/
def baseArgument  :
    (build I X T hA hB hC t ht).carrier.below
      ((build I X T hA hB hC t ht).carrier.cell c) :=
  ⟨(build I X T hA hB hC t ht).baseMap d, by rw [Layer.base_index, O.owner_index]; exact hd⟩

theorem row_base_source  :
    (build I X T hA hB hC t ht).rows.E c (O.baseArgument d hd) =
      source I X T hA hB hC O.birth O.height O.member
        ((build I X T hA hB hC O.birth O.height).baseMap d) := by
  let e : (build I X T hA hB hC O.birth O.height).carrier.below
      ((build I X T hA hB hC O.birth O.height).carrier.cell
        (owner I X T hA hB hC O.birth O.height O.member)) :=
    ⟨(build I X T hA hB hC O.birth O.height).baseMap d, by
      rw [Layer.base_index, GrowthPaddedNativeRows.owner_index]; exact hd⟩
  have he : O.domain e = O.baseArgument d hd := Subtype.ext
    ((O.domain_val e).trans (O.base d))
  rw [← he, O.row]

end

/-- Present original fields are literal numerical columns. The membership
premise only asserts presence; absent future fields use the shadow theorem. -/
theorem row_original d
    (hd : GradedLe (I.boundary.cell d) (A, O.birth + 2)) :
    (build I X T hA hB hC t ht).rows.E c
      (O.baseArgument (RelativeLadderLayer.old I.boundary (by omega : 0 < A.card) d)
        (by simpa only [RelativeLadderLayer.old_index] using hd)) =
      fields X (O.birth + 2) O.member (field I d) := by
  rw [row_base_source, source_original]

def ladderArgument (v : RelativeLadderLayer.Point
    (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1)) :
    (build I X T hA hB hC t ht).carrier.below
      ((build I X T hA hB hC t ht).carrier.cell c) :=
  O.baseArgument (RelativeLadderLayer.added I.boundary (by omega : 0 < A.card) v)
    (by rw [RelativeLadderLayer.added_index]; exact ⟨le_rfl, by omega⟩)

section
variable (v : RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1))

theorem row_ladder_source  :
    (build I X T hA hB hC t ht).rows.E c (O.ladderArgument v) =
      source I X T hA hB hC O.birth O.height O.member
        (ladder I X T hA hB hC O.birth O.height v) :=
  O.row_base_source _ _

/-- The full rank table, not merely represented-field readouts. -/
theorem row_ladder  :
    (build I X T hA hB hC t ht).rows.E c (O.ladderArgument v) =
      SupportLadderRows.image (RelativeLadderLayer.ranks (fields X 1))
        (anchor I X T hA hB hC O.birth O.height O.member)
        (LadderScalarRendering.level
          (LadderScalarRendering.values (fields X (O.birth + 2) O.member))
          (ceiling I O.birth)) v := by
  rw [O.row_ladder_source, source_ladder]

end

theorem row_shadow_sup f :
    (Finset.univ : Finset (Catalogue X 1)).sup
      (fun b => (build I X T hA hB hC t ht).rows.E c
        (O.ladderArgument (SupportLadderRows.shadow b f))) =
      fields X (O.birth + 2) O.member f := by
  simp only [O.row_ladder_source]
  exact source_shadow_sup I X T hA hB hC O.birth O.height O.member f

theorem row_spare :
    (build I X T hA hB hC t ht).rows.E c
      (O.ladderArgument (SupportLadderRows.leaf (by exact Nat.succ_pos _)
        (anchor I X T hA hB hC O.birth O.height O.member))) = ceiling I O.birth := by
  rw [O.row_ladder_source]
  exact source_spare I X T hA hB hC O.birth O.height O.member

theorem row_ceiling_at i (hi : 1 ≤ i) (hib : i ≤ O.birth + 2) :
    ∃ d,
      (build I X T hA hB hC t ht).carrier.cell d.1 = (A, i) ∧
        (build I X T hA hB hC t ht).rows.E c d = ceiling I O.birth := by
  obtain ⟨d, hd, hv⟩ := source_ceiling_at I X T hA hB hC O.birth O.height O.member i hi hib
  let e : (build I X T hA hB hC O.birth O.height).carrier.below
      ((build I X T hA hB hC O.birth O.height).carrier.cell
        (owner I X T hA hB hC O.birth O.height O.member)) :=
    ⟨d, by rw [hd, GrowthPaddedNativeRows.owner_index]; exact ⟨le_rfl, hib⟩⟩
  exact ⟨O.domain e, (congrArg _ (O.domain_val e)).trans ((O.index d).trans hd),
    (O.row e).trans hv⟩

end Origin

end
end VaughtConjecture.Knight.GrowthPaddedOwnerProvenance
