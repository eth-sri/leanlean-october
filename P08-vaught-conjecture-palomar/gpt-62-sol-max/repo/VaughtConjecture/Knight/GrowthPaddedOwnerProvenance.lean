/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedNativeRows

@[expose] public section

namespace VaughtConjecture.Knight.GrowthPaddedOwnerProvenance

open Transform Value ExtOrd Growth GrowthOrderedBase GrowthHigherSources

open GrowthPaddedContract GrowthPaddedIteration GrowthPaddedNativeRows

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (G : BuildContext A B C R m n J)

local notation "P" => G.tower
local notation "Fld" => Field G.I.right.scheme G.I.left.scheme
local notation "Pt" => RelativeLadderLayer.Point (X := Fld) (Q := Catalogue G.X 1)
local notation "B₀" => GrowthPaddedContract.base G.I G.X G.attach G.height G.leftProper G.rightProper

/-- The birth rows of a higher owner persist on actual occurrences in the
installed tower. Only the forward transport of its arguments is needed. -/
structure Origin (c : Cell (P).carrier) where
  birth : ℕ
  earlier : birth ≤ G.depth
  member : Catalogue G.X (birth + 2)
  map : Cell (G.earlier earlier).tower.carrier → Cell (P).carrier
  index : ∀ d, (P).carrier.cell (map d) = (G.earlier earlier).tower.carrier.cell d
  base : ∀ d, map ((G.earlier earlier).tower.baseMap d) = (P).baseMap d
  occurrence : map ((G.earlier earlier).tower.controller member).1 = c
  row : ∀ d : (G.earlier earlier).tower.carrier.below (A, birth + 2),
    (P).rows.E c ⟨map d.1, by
      rw [← occurrence, index, index, ((G.earlier earlier).tower.controller member).2]
      exact d.2⟩ = (G.earlier earlier).tower.source member d.1

namespace Origin

variable {G}
variable {c : Cell G.tower.carrier} (O : Origin G c)

abbrev birthContext := G.earlier O.earlier
abbrev anchor := O.birthContext.tower.baseAnchor O.member
abbrev ceiling := GrowthPaddedNativeRows.ceiling (I := G.I) O.birth

local notation "E₀" => O.birthContext.tower

theorem owner_index : (P).carrier.cell c = (A, O.birth + 2) :=
  (congrArg (P).carrier.cell O.occurrence).symm.trans
    ((O.index _).trans ((E₀).controller O.member).2)

def argument (d : (E₀).carrier.below (A, O.birth + 2)) :
    (P).carrier.below ((P).carrier.cell c) :=
  ⟨O.map d.1, by rw [O.index, O.owner_index]; exact d.2⟩

theorem row_argument (d : (E₀).carrier.below (A, O.birth + 2)) :
    (P).rows.E c (O.argument d) = (E₀).source O.member d.1 := O.row d

end Origin

private def native (a : Catalogue G.X (G.depth + 2)) : Origin G ((P).controller a).1 where
  birth := G.depth
  earlier := le_rfl
  member := a
  map := id
  index _ := rfl
  base _ := rfl
  occurrence := rfl
  row d := (P).controller_row a ⟨d.1, by rw [((P).controller a).2]; exact d.2⟩

section Successor

variable (t : ℕ) (ht : (t + 1) + 2 ≤ A.card)

local notation "L" => G.atDepth t (by omega)
local notation "H" => G.atDepth (t + 1) ht
local notation "up" => Padded.StepRows.old (BuildContext.tower L) ht

private def inherit (c : Cell (L).tower.carrier) (O : Origin L c) : Origin H (up c) where
  birth := O.birth
  earlier := O.earlier.trans (Nat.le_succ t)
  member := O.member
  map d := up (O.map d)
  index d := (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans (O.index d)
  base d := congrArg up (O.base d)
  occurrence := congrArg up O.occurrence
  row d := (Padded.StepRows.inherited_row (L).tower (Nat.le_add_left 2 t) ht c (O.argument d)).trans
    (O.row_argument d)

end Successor

/-- Exhaustive actual-owner provenance, including every inherited layer. -/
theorem exists_origin_at (t : ℕ) (ht : t + 2 ≤ A.card)
    (c : Cell (G.atDepth t ht).tower.carrier)
    (hc : (G.atDepth t ht).tower.carrier.scope c = A)
    (hg : 2 ≤ (G.atDepth t ht).tower.carrier.grade c) :
    Nonempty (Origin (G.atDepth t ht) c) := by
  induction t with
  | zero =>
    rcases GrowthPaddedSuccessor.cell_cases G.I G.X G.attach G.height G.leftProper G.rightProper c with
      ⟨d, rfl⟩ | ⟨a, rfl⟩
    · have hi : (G.atDepth 0 ht).tower.carrier.cell
          (GrowthPaddedSuccessor.old G.I G.X G.attach G.height G.leftProper G.rightProper d) =
          (B₀).cell d := SourceLayerCarrier.cell_toCell _ _ _ _ _ _
      have hs : (B₀).scope d = A := (congrArg Prod.fst hi).symm.trans hc
      have hh : 2 ≤ (B₀).grade d := hg.trans_eq (congrArg Prod.snd hi)
      have h := (spec G.I G.X G.attach G.height G.leftProper G.rightProper).base_full_grade d hs
      exact (Nat.not_succ_le_self 1 (hh.trans_eq h)).elim
    · exact ⟨native (G.atDepth 0 ht) a⟩
  | succ t ih =>
    let L := (G.atDepth t (by omega)).tower
    obtain ⟨x, hx⟩ := (SourceLayerCarrier.enumeration L.carrier
      (Catalogue G.X (t + 2 + 1)) (t + 2 + 1) (Nat.succ_pos _) (by omega)).surjective c
    change SourceLayerCarrier.toCell _ _ _ _ _ x = c at hx
    rcases x with d | a
    · rw [← hx] at hc hg ⊢
      have hi := SourceLayerCarrier.cell_toCell L.carrier (Catalogue G.X (t + 2 + 1))
          (t + 2 + 1) (Nat.succ_pos _) (by omega) (.inl d)
      obtain ⟨O⟩ := ih (by omega) d ((congrArg Prod.fst hi).symm.trans hc)
        (hg.trans_eq (congrArg Prod.snd hi))
      exact ⟨inherit G t ht d O⟩
    · rw [← hx]
      exact ⟨native (G.atDepth (t + 1) ht) a⟩

/-- Chosen provenance from the actual inventory. -/
def origin (c : Cell (P).carrier) (hc : (P).carrier.scope c = A)
    (hg : 2 ≤ (P).carrier.grade c) : Origin G c :=
  Classical.choice (exists_origin_at G G.depth G.fits c hc hg)

namespace Origin

variable {G}
variable {c : Cell G.tower.carrier} (O : Origin G c)

local notation "E₀" => O.birthContext.tower

theorem row_diagonal : (P).rows.E c ⟨c, GradedLe.refl _⟩ = O.ceiling := by
  let b := (E₀).controller O.member
  have hb : (E₀).carrier.cell b.1 = (A, O.birth + 2) := b.2
  exact ((P).rows.E_congr rfl O.occurrence.symm).trans
    ((O.row_argument ⟨b.1, ⟨(congrArg Prod.fst hb).le, (congrArg Prod.snd hb).le⟩⟩).trans ((E₀).source_diagonal O.member))

def baseArgument (d : Cell B₀) (hd : GradedLe ((B₀).cell d) (A, O.birth + 2)) :
    (P).carrier.below ((P).carrier.cell c) :=
  ⟨(P).baseMap d, by rw [Padded.Layer.base_index, O.owner_index]; exact hd⟩

theorem row_base_source (d : Cell B₀) (hd : GradedLe ((B₀).cell d) (A, O.birth + 2)) :
    (P).rows.E c (O.baseArgument d hd) = (E₀).source O.member ((E₀).baseMap d) :=
  ((P).rows.E_congr rfl (O.base d).symm).trans
    (O.row_argument ⟨(E₀).baseMap d, ((E₀).base_index d) ▸ hd⟩)

def originalArgument (d : Cell G.I.boundary)
    (hd : GradedLe (G.I.boundary.cell d) (A, O.birth + 2)) :
    (P).carrier.below ((P).carrier.cell c) :=
  O.baseArgument (RelativeLadderLayer.old G.I.boundary G.pos d)
    (by simpa only [RelativeLadderLayer.old_index] using hd)

/-- Present originals are literal columns; future fields use shadow maxima. -/
theorem row_original (d : Cell G.I.boundary) (hd : GradedLe (G.I.boundary.cell d) (A, O.birth + 2)) :
    (P).rows.E c (O.originalArgument d hd) = fields G.X (O.birth + 2) O.member (field G.I d) :=
  (O.row_base_source _ _).trans ((E₀).source_original O.member d)

def ladderArgument (v : Pt) : (P).carrier.below ((P).carrier.cell c) :=
  O.baseArgument (RelativeLadderLayer.added G.I.boundary G.pos v)
    (by rw [RelativeLadderLayer.added_index]; exact ⟨le_rfl, by omega⟩)

theorem row_ladder_source (v : Pt) : (P).rows.E c (O.ladderArgument v) =
    (E₀).source O.member (ladder O.birthContext v) := O.row_base_source _ _

/-- The full rank table, not merely represented-field readouts. -/
theorem row_ladder (v : Pt) : (P).rows.E c (O.ladderArgument v) =
    SupportLadderRows.image (RelativeLadderLayer.ranks (fields G.X 1)) O.anchor
      (LadderScalarRendering.level (LadderScalarRendering.values (fields G.X (O.birth + 2) O.member))
        O.ceiling) v :=
  (O.row_ladder_source v).trans (source_ladder O.birthContext O.member v)

theorem row_shadow_sup (f : Fld) : (Finset.univ : Finset (Catalogue G.X 1)).sup
    (fun b => (P).rows.E c (O.ladderArgument (SupportLadderRows.shadow b f))) =
      fields G.X (O.birth + 2) O.member f := by
  simp only [O.row_ladder_source]
  exact source_shadow_sup O.birthContext O.member f

theorem row_spare : (P).rows.E c (O.ladderArgument (SupportLadderRows.leaf (Nat.succ_pos _) O.anchor)) =
    O.ceiling :=
  (O.row_ladder_source _).trans (source_spare O.birthContext O.member)

theorem row_ceiling_at (i : ℕ) (hi : 1 ≤ i) (hib : i ≤ O.birth + 2) :
    ∃ d : (P).carrier.below ((P).carrier.cell c),
      (P).carrier.cell d.1 = (A, i) ∧ (P).rows.E c d = O.ceiling := by
  obtain ⟨d, hd, hv⟩ := (E₀).source_ceiling_at O.member i hi hib
  let e : (E₀).carrier.below (A, O.birth + 2) := ⟨d, hd ▸ ⟨le_rfl, hib⟩⟩
  exact ⟨O.argument e, (O.index d).trans hd, (O.row_argument e).trans hv⟩

end Origin

end

end VaughtConjecture.Knight.GrowthPaddedOwnerProvenance
