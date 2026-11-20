/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFrame
public import VaughtConjecture.Knight.GrowthHigherMixedExtensionValue

/-! # Every owner of the higher mixed extension is lawful

Grade-one owners reuse the constructed uncapped base section. Original owners
use the literal inherited restriction of the lawful boundary projection.
Every higher auxiliary uses its own prescribed locality witness, with the
constructed lower-ceiling bounds protecting the grade-dependent targets.
-/

@[expose] public section

namespace VaughtConjecture.Knight.GrowthHigherMixed
open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources
open GrowthPaddedContract GrowthPaddedIteration SupportLadderRows
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : I.GrowthData}
  (frame : I.GrowthFrame X)
  (t : ℕ) (ht : t + 2 ≤ A.card)
local notation "P" => tower frame t ht
local notation "D" => carrier frame t ht
local notation "Rows" => rows frame t ht

variable (U : Finset ι) (hU : U ∈ R)
  (hm : U = A ∨ ScopeReplicationCarrier.Mixed B C U)
  (j : ℕ) (hj : j ≤ U.card) (hj0 : 1 ≤ j)
  {p : CellScheme.below (carrier frame t ht) (U, j) → ExtOrd}

theorem native_one_lawful (hp : RespectsSemanticsBelow Rows (U, j) p) :
    RespectsSemanticsBelow (P).rows (A, 1)
      (fun d => nativeValue frame t ht U hU hm j hj hj0 p d.1) := by
  have hplan : U ∈ (P).carrier.plan := by rw [GrowthPaddedIteration.build_plan]; exact hU
  let q : (D).SectionAt (U, 1) := fun d => p (CellScheme.below.mono
    (show GradedLe (U, 1) (U, j) from ⟨le_rfl, hj0⟩) d)
  have hq : RespectsSemanticsBelow Rows (U, 1) q :=
    hp.mono (show GradedLe (U, 1) (U, j) from ⟨le_rfl, hj0⟩)
  obtain ⟨a, τ, hτ, hmax, hb, hread, -⟩ :=
    GrowthMixedGradeOne.exists_spare_chart frame P U hplan hm hq
  have hl := GrowthMixedGradeOne.layerSection_lawful frame P U hplan hm
    hτ hq hmax hb hread
  have he : (fun d : (P).carrier.below (A, 1) =>
      nativeValue frame t ht U hU hm j hj hj0 p d.1) =
      fun d => GrowthMixedGradeOne.layerSection frame P a τ d.1 := by
    funext d
    obtain ⟨b, hb⟩ := GrowthMixedGradeOne.eq_baseMap_of_grade_le_one frame P d.1 d.2.2
    rcases RelativeLadderLayer.cell_cases I.boundary frame.positive b with
        ⟨e, rfl⟩ | ⟨v, rfl⟩
    · have hge : I.boundary.grade e ≤ 1 :=
        (congrArg Prod.snd (original_index frame t ht e)).symm.le.trans
          ((congrArg (P).carrier.grade hb).symm.le.trans d.2.2)
      rw [hb]
      change nativeValue frame t ht U hU hm j hj hj0 p
        (original frame t ht e) = _
      rw [native_original, boundaryValue, height, ite_eq_left hge, min_top_right,
        GrowthMixedGradeOne.layerSection_baseMap,
        GrowthSpareRecognition.ladderRow_spare_old I X frame.height a e]
      exact GrowthMixedGradeOne.shadowSup_eq_spare frame P U hplan hm hτ hread _
    · have hvs : (P).carrier.scope ((P).baseMap (RelativeLadderLayer.added
          I.boundary frame.positive v)) = A :=
        congrArg Prod.fst (ladder_index frame t ht v)
      have hvg : (P).carrier.grade ((P).baseMap (RelativeLadderLayer.added
          I.boundary frame.positive v)) ≤ j :=
        (congrArg Prod.snd (ladder_index frame t ht v)).le.trans hj0
      rw [hb, native_full frame t ht U hU hm j hj hj0 p _ hvs hvg,
        GrowthMixedGradeOne.layerSection_baseMap,
        GrowthSpareRecognition.ladderRow_spare_added I X frame.height a v]
      exact (hread v).symm
  exact he.symm ▸ hl

theorem original_respects (hp : RespectsSemanticsBelow Rows (U, j) p) (hjt : j ≤ t + 2)
    (c : Cell I.boundary) (hc : I.boundary.grade c ≤ j) :
    RespectsSemanticsBelow (P).rows ((P).carrier.cell (original frame t ht c))
      (fun d => nativeValue frame t ht U hU hm j hj hj0 p d.1) := by
  apply ((P).base_respects (RelativeLadderLayer.old I.boundary frame.positive c)
    (nativeValue frame t ht U hU hm j hj hj0 p)).mpr
  apply (RelativeLadderLayer.old_respects_iff I.boundary I.rows frame.positive
    (GrowthOrderedBase.field I) (fields X 1) (GrowthOrderedBase.proper I frame.leftProper frame.rightProper) c _).mpr
  have hl := (boundary_projection frame t ht U hU hm j hj hj0 hp hjt).mono
    (show GradedLe (I.boundary.cell c) (A, j) from
      ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan c), hc⟩)
  have he : (fun d : I.boundary.RowDomain c =>
      nativeValue frame t ht U hU hm j hj hj0 p
        (original frame t ht d.1)) =
      fun d => boundaryValue frame t ht U hU hm j hj hj0 p d.1 :=
    funext fun d => native_original frame t ht U hU hm j hj hj0 p d.1
  change RespectsSemanticsBelow I.rows (I.boundary.cell c) (fun d =>
    nativeValue frame t ht U hU hm j hj hj0 p (original frame t ht d.1))
  rw [he]
  exact hl

theorem owner_le_height (hp : RespectsSemanticsBelow Rows (U, j) p) (hjt : j ≤ t + 2)
    (c : Cell (P).carrier) (hc : (P).carrier.scope c = A)
    (hg : (P).carrier.grade c ≤ j) (hg2 : 2 ≤ (P).carrier.grade c)
    (i : ℕ) (hi : i ≤ (P).carrier.grade c) :
    p (place frame t ht U hU hm j hj c hc hg) ≤
      height frame t ht U j p i := by
  unfold height
  by_cases hi1 : i ≤ 1
  · rw [ite_eq_left hi1]; exact le_top
  rw [ite_eq_right hi1, ite_eq_left (hi.trans hg)]
  exact (le_gradeMax frame t ht U j p _ _
    (congrArg Prod.snd (place_index frame t ht U hU hm j hj c hc hg))).trans
      (gradeMax_antitone frame t ht U hU hm j hj hp i ((P).carrier.grade c)
        (by omega) hg2 hi hg (hg.trans hjt))

theorem higher_locality (hp : RespectsSemanticsBelow Rows (U, j) p) (hjt : j ≤ t + 2)
    (c : Cell (P).carrier) (hc : (P).carrier.scope c = A)
    (hg : (P).carrier.grade c ≤ j) (hg2 : 2 ≤ (P).carrier.grade c) :
    TransformsTo (fun d : (P).carrier.RowDomain c => (P).carrier.grade d.1)
      ((P).rows.E c) (fun d => min
        (nativeValue frame t ht U hU hm j hj hj0 p d.1)
        (nativeValue frame t ht U hU hm j hj hj0 p c)) := by
  let O := GrowthPaddedOwnerProvenance.origin frame t ht c hc hg2
  obtain ⟨τ, hτ, hr⟩ := exists_owner_chart frame t ht U hU hm j hj hp c hc hg
  apply hτ.transformsTo
  intro d
  rw [gTop_of_le (show (P).carrier.grade d.1 ≤ (P).carrier.grade c from d.2.2), min_top_right,
    native_full frame t ht U hU hm j hj hj0 p c hc hg]
  rcases original_or_full frame t ht d.1 with ⟨e, he⟩ | hdf
  · have hed : GradedLe (I.boundary.cell e) ((P).carrier.cell c) :=
      (original_index frame t ht e) ▸ (he ▸ d.2)
    have hs : (P).rows.E c d = fields X (O.birth + 2) O.member (GrowthOrderedBase.field I e) :=
      ((P).rows.E_congr rfl he).trans (O.row_original e (O.owner_index ▸ hed))
    rw [hs, owner_recognition frame t ht U hU hm j hj hj0 c hc hg O hτ hr,
      he, native_original, boundaryValue, min_assoc,
      min_eq_right (owner_le_height frame t ht U hU hm j hj hp hjt
        c hc hg hg2 (I.boundary.grade e) hed.2)]
  · have hgd := d.2.2.trans hg
    have hz : (D).grade (place frame t ht U hU hm j hj d.1 hdf hgd).1 ≤
        (P).carrier.grade c :=
      (congrArg Prod.snd (place_index frame t ht U hU hm j hj d.1 hdf hgd)).le.trans d.2.2
    have he : (P).rows.E c (nativeArgument frame t ht U j c hc
        (place frame t ht U hU hm j hj d.1 hdf hgd) hz) = (P).rows.E c d :=
      (P).rows.E_congr rfl (erase_place frame t ht U hU hm j hj d.1 hdf hgd)
    rw [native_full frame t ht U hU hm j hj hj0 p d.1 hdf hgd]
    exact (hr _ hz).symm.trans (congrArg τ he)

end
end VaughtConjecture.Knight.GrowthHigherMixed
