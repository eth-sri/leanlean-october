/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GrowthHigherMixedExtensionValue

/-! # Every owner of the higher mixed extension is lawful

Grade-one owners reuse the constructed uncapped base section. Original owners
use the literal inherited restriction of the lawful boundary projection.
Every higher auxiliary uses its own prescribed locality witness, with the
constructed lower-ceiling bounds protecting the grade-dependent targets.
-/

namespace VaughtConjecture.Knight.GrowthHigherMixed
open AmalgamationPlan Transform   Growth GrowthHigherSources
open GrowthPaddedContract GrowthPaddedIteration 

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  (t : ℕ) (ht : t + 2 ≤ A.card)
local notation "P" => tower I X T hA hB hC t ht
local notation "D" => carrier I X T hA hB hC t ht
local notation "Rows" => rows I X T hA hB hC t ht

variable (U : Finset ι) (hU : U ∈ R)
  (hm : U = A ∨ ScopeReplicationCarrier.Mixed B C U)
  (j : ℕ) (hj : j ≤ U.card) (hj0 : 1 ≤ j)
  {p : CellScheme.below (carrier I X T hA hB hC t ht) (U, j) → ExtOrd}

local notation "nativeValue₀" => nativeValue I X T hA hB hC t ht U hU hm j hj hj0

local notation "native_full₀" => native_full hU hm hj hj0

local notation "original₀" => original I X T hA hB hC t ht

theorem native_one_lawful (hp : RespectsSemanticsBelow Rows (U, j) p) :
    RespectsSemanticsBelow (P).rows (A, 1)
      (fun d => nativeValue₀ p d.1) := by
  have hplan : U ∈ (P).carrier.plan := by rw [GrowthPaddedIteration.build_plan]; exact hU
  let q  := fun d => p (CellScheme.below.mono
    (show GradedLe (U, 1) (U, j) from ⟨le_rfl, hj0⟩) d)
  have hq : RespectsSemanticsBelow Rows (U, 1) q :=
    hp.mono (show GradedLe (U, 1) (U, j) from ⟨le_rfl, hj0⟩)
  obtain ⟨a, τ, hτ, hmax, hb, hread, -⟩ :=
    GrowthMixedGradeOne.exists_spare_chart I X T hA hB hC P U hplan hm hq
  have hl := GrowthMixedGradeOne.layerSection_lawful I X T hA hB hC P U hplan hm
    hτ hq hmax hb hread
  have he : (fun d : (P).carrier.below (A, 1) =>
      nativeValue₀ p d.1) =
      fun d => GrowthMixedGradeOne.layerSection I X T hA hB hC P a τ d.1 := by
    funext d
    obtain ⟨b, hb⟩ := GrowthMixedGradeOne.eq_baseMap_of_grade_le_one I X T hA hB hC P d.1 d.2.2
    rcases RelativeLadderLayer.cell_cases b with
        ⟨e, rfl⟩ | ⟨v, rfl⟩
    · have hge : I.boundary.grade e ≤ 1 :=
        (congrArg Prod.snd (original_index T hA hB hC ht e)).symm.le.trans
          ((congrArg (P).carrier.grade hb).symm.le.trans d.2.2)
      rw [hb]
      change nativeValue₀ p
        (original₀ e) = _
      rw [native_original, boundaryValue, height, ite_eq_left hge, min_top_right,
        GrowthMixedGradeOne.layerSection_baseMap,
        GrowthSpareRecognition.ladderRow_spare_old I X hA a e]
      exact GrowthMixedGradeOne.shadowSup_eq_spare I X T hA hB hC P U hplan hm hτ hread _
    · have hvs : (P).carrier.scope ((P).baseMap (RelativeLadderLayer.added
          I.boundary (by omega : 0 < A.card) v)) = A :=
        congrArg Prod.fst (ladder_index T hA hB hC ht v)
      have hvg  :=
        (congrArg Prod.snd (ladder_index T hA hB hC ht v)).le.trans hj0
      rw [hb, native_full₀ p _ hvs hvg,
        GrowthMixedGradeOne.layerSection_baseMap,
        GrowthSpareRecognition.ladderRow_spare_added I X hA a v]
      exact (hread v).symm
  exact he.symm ▸ hl

theorem original_respects (hp : RespectsSemanticsBelow Rows (U, j) p) (hjt : j ≤ t + 2)
    c (hc : I.boundary.grade c ≤ j) :
    RespectsSemanticsBelow (P).rows ((P).carrier.cell (original₀ c))
      (fun d => nativeValue₀ p d.1) := by
  apply ((P).base_respects (RelativeLadderLayer.old I.boundary (by omega : 0 < A.card) c)
    (nativeValue₀ p)).mpr
  apply (RelativeLadderLayer.old_respects_iff c _).mpr
  have hl := (boundary_projection hU hm hj hj0 hp hjt).mono
    (show GradedLe (I.boundary.cell c) (A, j) from
      ⟨I.boundary.scope_subset c, hc⟩)
  have he : (fun d : I.boundary.belowCell c =>
      nativeValue₀ p
        (original₀ d.1)) =
      fun d => boundaryValue I X T hA hB hC t ht U hU hm j hj hj0 p d.1 :=
    funext fun d => native_original I X T hA hB hC t ht U hU hm j hj hj0 p d.1
  change Semantics.RowLawful I.rows c (fun d =>
    nativeValue₀ p (original₀ d.1))
  rw [he]
  exact hl

local notation "place₀" => place I X T hA hB hC t ht U hU hm j hj

theorem owner_le_height (hp : RespectsSemanticsBelow Rows (U, j) p) (hjt : j ≤ t + 2)
    c (hc : (P).carrier.scope c = A)
    (hg : (P).carrier.grade c ≤ j) (hg2 : 2 ≤ (P).carrier.grade c)
    i (hi : i ≤ (P).carrier.grade c) :
    p (place₀ c hc hg) ≤
      height I X T hA hB hC t ht U j p i := by
  unfold height
  by_cases hi1 : i ≤ 1
  · rw [ite_eq_left hi1]; exact le_top
  rw [ite_eq_right hi1, ite_eq_left (hi.trans hg)]
  exact (le_gradeMax p _ _
    (congrArg Prod.snd (place_index hU hm hj c hc hg))).trans
      (gradeMax_antitone I X T hA hB hC t ht U hU hm j hj hp i ((P).carrier.grade c)
        (by omega) hg2 hi hg (hg.trans hjt))

theorem higher_locality (hp : RespectsSemanticsBelow Rows (U, j) p) (hjt : j ≤ t + 2)
    c (hc : (P).carrier.scope c = A)
    (hg : (P).carrier.grade c ≤ j) (hg2 : 2 ≤ (P).carrier.grade c) :
    TransformsTo (fun d => (P).carrier.grade d.1)
      ((P).rows.E c) (fun d => min
        (nativeValue₀ p d.1)
        (nativeValue₀ p c)) := by
  let O := GrowthPaddedOwnerProvenance.origin hc hg2
  obtain ⟨τ, hτ, hr⟩ := exists_owner_chart hU hm hj hp
  apply hτ.transformsTo
  intro d
  rw [gTop_of_le (show (P).carrier.grade d.1 ≤ (P).carrier.grade c from d.2.2), min_top_right,
    native_full₀ p c hc hg]
  rcases original_or_full d.1 with ⟨e, he⟩ | hdf
  · have hed : GradedLe (I.boundary.cell e) ((P).carrier.cell c) :=
      (original_index T hA hB hC ht e) ▸ (he ▸ d.2)
    have hs : (P).rows.E c d = fields X (O.birth + 2) O.member (GrowthOrderedBase.field I e) :=
      ((P).rows.E_congr rfl he).trans (O.row_original e (O.owner_index ▸ hed))
    rw [hs, owner_recognition hj0 O hτ hr,
      he, native_original, boundaryValue, min_assoc,
      min_eq_right (owner_le_height I X T hA hB hC t ht U hU hm j hj hp hjt
        c hc hg hg2 (I.boundary.grade e) hed.2)]
  · have hgd := d.2.2.trans hg
    have hz  :=
      (congrArg Prod.snd (place_index hU hm hj d.1 hdf hgd)).le.trans d.2.2
    have he : (P).rows.E c (nativeArgument c hc
        (place₀ d.1 hdf hgd) hz) = (P).rows.E c d :=
      (P).rows.E_congr rfl (erase_place hU hm hj d.1 hdf hgd)
    rw [native_full₀ p d.1 hdf hgd]
    exact (hr _ hz).symm.trans (congrArg τ he)


