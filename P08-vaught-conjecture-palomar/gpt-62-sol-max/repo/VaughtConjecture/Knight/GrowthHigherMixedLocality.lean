/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthHigherMixedExtensionValue

@[expose] public section

namespace VaughtConjecture.Knight.GrowthHigherMixed

open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources

open GrowthPaddedContract GrowthPaddedIteration SupportLadderRows

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (G : GrowthPaddedIteration.BuildContext A B C R m n J)

local notation "P" => G.tower

local notation "D" => carrier G

local notation "Rows" => rows G

variable {G} (W : Cut G)
  {p : CellScheme.below (carrier G) W.index → ExtOrd}

theorem native_one_lawful (hp : RespectsSemanticsBelow Rows W.index p) :
    RespectsSemanticsBelow (P).rows (A, 1)
      (fun d => nativeValue W p d.1) := by
  have hq := hp.mono W.gradeOne
  obtain ⟨Ch⟩ := GrowthMixedGradeOne.exists_spare_chart W hq
  have hl := Ch.layerSection_lawful hq
  have he : (fun d : (P).carrier.below (A, 1) =>
      nativeValue W p d.1) =
      fun d => Ch.layerSection d.1 := by
    funext d
    obtain ⟨b, hb⟩ := GrowthMixedGradeOne.eq_baseMap_of_grade_le_one G d.1 d.2.2
    rcases RelativeLadderLayer.cell_cases G.I.boundary G.pos b with
        ⟨e, rfl⟩ | ⟨v, rfl⟩
    · have hge : G.I.boundary.grade e ≤ 1 :=
        (congrArg Prod.snd (original_index G e)).symm.le.trans
          ((congrArg (P).carrier.grade hb).symm.le.trans d.2.2)
      rw [hb]
      change nativeValue W p
        (original G e) = _
      rw (config := { transparency := .default }) [native_original, boundaryValue, height, ite_eq_left hge, min_top_right,
        Ch.layerSection_baseMap,
        GrowthSpareRecognition.ladderRow_spare_old G.I G.X G.height Ch.a e]
      exact Ch.shadowSup_eq_spare _
    · have hvs : (P).carrier.scope ((P).baseMap (RelativeLadderLayer.added
          G.I.boundary G.pos v)) = A :=
        congrArg Prod.fst (ladder_index G v)
      have hvg : (P).carrier.grade ((P).baseMap (RelativeLadderLayer.added
          G.I.boundary G.pos v)) ≤ W.grade :=
        (congrArg Prod.snd (ladder_index G v)).le.trans W.pos
      rw (config := { transparency := .default }) [hb, native_full W p _ hvs hvg,
        Ch.layerSection_baseMap,
        GrowthSpareRecognition.ladderRow_spare_added G.I G.X G.height Ch.a v]
      exact (Ch.ladder v).symm
  exact he.symm ▸ hl

theorem original_respects (hp : RespectsSemanticsBelow Rows W.index p)
    (c : Cell G.I.boundary) (hc : G.I.boundary.grade c ≤ W.grade) :
    RespectsSemanticsBelow (P).rows ((P).carrier.cell (original G c))
      (fun d => nativeValue W p d.1) := by
  apply ((P).base_respects (RelativeLadderLayer.old G.I.boundary G.pos c)
    (nativeValue W p)).mpr
  apply (RelativeLadderLayer.old_respects_iff G.I.boundary G.I.rows G.pos
    (GrowthOrderedBase.field G.I) (fields G.X 1) (GrowthOrderedBase.proper G.I G.leftProper G.rightProper) c _).mpr
  have hl := (boundary_projection W hp).mono
    (show GradedLe (G.I.boundary.cell c) (A, W.grade) from
      ⟨G.I.boundary.scope_subset c, hc⟩)
  have he : (fun d : G.I.boundary.below (G.I.boundary.cell c) =>
      nativeValue W p
        (original G d.1)) =
      fun d => boundaryValue W p d.1 :=
    funext fun d => native_original W p d.1
  change RespectsSemanticsBelow G.I.rows (G.I.boundary.cell c) (fun d =>
    nativeValue W p (original G d.1))
  rw [he]
  exact hl

theorem owner_le_height (hp : RespectsSemanticsBelow Rows W.index p)
    (c : Cell (P).carrier) (hc : (P).carrier.scope c = A)
    (hg : (P).carrier.grade c ≤ W.grade) (hg2 : 2 ≤ (P).carrier.grade c)
    (i : ℕ) (hi : i ≤ (P).carrier.grade c) :
    p (place W c hc hg) ≤
      height W p i := by
  unfold height
  by_cases hi1 : i ≤ 1
  · simp_all
  rw [ite_eq_right hi1, ite_eq_left (hi.trans hg)]
  exact (le_gradeMax W p _ _
    (congrArg Prod.snd (place_index W c hc hg))).trans
      (gradeMax_antitone W hp i ((P).carrier.grade c)
        (by omega) hg2 hi hg)

theorem higher_locality (hp : RespectsSemanticsBelow Rows W.index p)
    (c : Cell (P).carrier) (hc : (P).carrier.scope c = A)
    (hg : (P).carrier.grade c ≤ W.grade) (hg2 : 2 ≤ (P).carrier.grade c) :
    TransformsTo (fun d : (P).carrier.below ((P).carrier.cell c) => (P).carrier.grade d.1)
      ((P).rows.E c) (fun d => min
        (nativeValue W p d.1)
        (nativeValue W p c)) := by
  obtain ⟨Ch⟩ := exists_owner_chart W hp c hc hg hg2
  let O := Ch.origin
  apply Ch.witness.transformsTo
  intro d
  rw [gTop_of_le (show (P).carrier.grade d.1 ≤ (P).carrier.grade c from d.2.2), min_top_right,
    native_full W p c hc hg]
  rcases original_or_full G d.1 with ⟨e, he⟩ | hdf
  · have hed : GradedLe (G.I.boundary.cell e) ((P).carrier.cell c) :=
      (original_index G e) ▸ (he ▸ d.2)
    have hs : (P).rows.E c d = fields G.X (O.birth + 2) O.member (GrowthOrderedBase.field G.I e) :=
      ((P).rows.E_congr rfl he).trans (O.row_original e (O.owner_index ▸ hed))
    rw [hs, Ch.recognition,
      he, native_original, boundaryValue, min_assoc,
      min_eq_right (owner_le_height W hp
        c hc hg hg2 (G.I.boundary.grade e) hed.2)]
  · have hgd := d.2.2.trans hg
    rw [native_full W p d.1 hdf hgd]
    exact (Ch.row _ d (erase_place W d.1 hdf hgd)).symm

end

end VaughtConjecture.Knight.GrowthHigherMixed
