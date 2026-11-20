/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthHigherMixedRecognition

@[expose] public section

namespace VaughtConjecture.Knight.GrowthHigherMixed

open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources

open GrowthPaddedContract GrowthPaddedIteration SupportLadderRows LadderScalarRendering

open SharpWitnessComposition

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (G : GrowthPaddedIteration.BuildContext A B C R m n J)

local notation "P" => G.tower

local notation "D" => carrier G

local notation "Rows" => rows G

local notation "Fld" => Field G.I.right.scheme G.I.left.scheme

local notation "ranks₁" => RelativeLadderLayer.ranks (fields G.X 1)

local notation "rungs" => RelativeLadderLayer.rungs (X := Fld)

variable {G} (W : Cut G)
  {p : CellScheme.below (carrier G) W.index → ExtOrd}

theorem original_readback_one (hp : RespectsSemanticsBelow Rows W.index p)
    (z : (D).below W.index) (d : Cell G.I.boundary)
    (hz : erase G z.1 = original G d)
    (hg : (D).grade z.1 = 1) :
    p z = shadowSup W p (GrowthOrderedBase.field G.I d) := by
  exact GrowthMixedGradeOne.original_readback_one W
    (hp.mono W.gradeOne)
    ⟨z.1, z.2.1, hg.le⟩ d hz

theorem boundary_one (hp : RespectsSemanticsBelow Rows W.index p) :
    RespectsSemanticsBelow G.I.rows (A, 1)
      (fun d => shadowSup W p
        (GrowthOrderedBase.field G.I d.1)) := by
  have hq := hp.mono W.gradeOne
  obtain ⟨Ch⟩ := GrowthMixedGradeOne.exists_spare_chart W hq
  have hl := RelativeLadderLayer.rank_respects G.I.boundary G.I.rows (GrowthOrderedBase.field G.I)
    (fields G.X 1) Ch.a (GrowthHigherSources.anchor_lawful_at G.I G.X G.attach Ch.a) rungs
  have he : (fun d : G.I.boundary.below (A, 1) =>
      shadowSup W p (GrowthOrderedBase.field G.I d.1)) =
      fun d => Ch.read (SupportLadderRows.source rungs (ranks₁ Ch.a (GrowthOrderedBase.field G.I d.1))) :=
    funext fun d => Ch.shadowSup_eq_spare _
  rw [he]
  by_cases hz : GrowthMixedGradeOne.spareSup W (p ∘ CellScheme.below.mono W.gradeOne) = ⊥
  · have htau : ∀ x, Ch.read x = ⊥ := fun x => le_bot_iff.mp ((Ch.bound x).trans_eq hz)
    simp only [htau]
    apply respectsBelow_bot
  · apply map_respects_of_bottom_reflection hl (fun d => d.2.2) (Ch.witness.bounded)
    intro d
    have hr := Ch.bottom_reflection hq hz (shadow Ch.a (GrowthOrderedBase.field G.I d.1))
    rwa [GrowthSpareRecognition.row_spare, GrowthLeafRecognition.index_shadow_self] at hr

/-- Heights outside the observed range are bottom only to give a globally
antitone function; no occurrence of that range is projected. -/
def height (p : (D).below W.index → ExtOrd) (k : ℕ) : ExtOrd :=
  if k ≤ 1 then ⊤ else if k ≤ W.grade then gradeMax W p k else ⊥

theorem height_antitone (hp : RespectsSemanticsBelow Rows W.index p) :
    Antitone (height W p) := by
  intro a b hab
  by_cases hb : b ≤ 1
  · simp [height, ite_eq_left hb, ite_eq_left (hab.trans hb), le_refl]
  by_cases ha : a ≤ 1
  · rw [height, height, ite_eq_left ha]
    exact le_top
  by_cases hbj : b ≤ W.grade
  · simp only [height, ite_eq_right hb, ite_eq_right ha,
      ite_eq_left hbj, ite_eq_left (hab.trans hbj)]
    exact gradeMax_antitone W hp a b
      (by omega) (by omega) hab hbj
  · simp [height, ite_eq_right hb, ite_eq_right hbj, bot_le]

/-- One lawful vector on the entire original boundary, including hidden
owners, preserving lower values above later grade maxima. -/
theorem boundary_projection (hp : RespectsSemanticsBelow Rows W.index p) :
    RespectsSemanticsBelow G.I.rows (A, W.grade) (fun d =>
      min (shadowSup W p (GrowthOrderedBase.field G.I d.1))
        (height W p (G.I.boundary.grade d.1))) := by
  apply GradePrefixProjection.respectsBelow (sem := G.I.rows) (BJ := (A, W.grade))
    (ρ := fun d => shadowSup W p (GrowthOrderedBase.field G.I d))
    (height_antitone W hp)
  intro k hkj
  by_cases hk0 : k = 0
  · subst k
    exact GrowthSpareRecognition.respectsBelow_zero G.I.rows _
  by_cases hk1 : k = 1
  · subst k
    simpa [height, ite_eq_left (le_refl (1 : ℕ)), min_top_right] using
      boundary_one W hp
  · simpa [height, ite_eq_right (by omega : ¬ k ≤ 1), ite_eq_left hkj] using
      boundary_capped_lawful W hp k
        (by omega) hkj

theorem projection_readback (hp : RespectsSemanticsBelow Rows W.index p)
    (z : (D).below W.index) (d : Cell G.I.boundary)
    (hz : erase G z.1 = original G d) :
    p z = min (shadowSup W p (GrowthOrderedBase.field G.I d))
      (height W p (G.I.boundary.grade d)) := by
  have hg : G.I.boundary.grade d = (D).grade z.1 :=
    (congrArg Prod.snd (original_index G d)).symm.trans
      ((congrArg (P).carrier.grade hz).symm.trans (ScopeReplicationCarrier.erase_grade (GrowthReplicatedRows.frame P) z.1))
  have hpos := (D).grade_pos z.1
  have hle : (D).grade z.1 ≤ W.grade := z.2.2
  rw [height, hg]
  by_cases h1 : (D).grade z.1 ≤ 1
  · rw [ite_eq_left h1, min_top_right]
    exact original_readback_one W hp z d hz (by omega)
  · rw [ite_eq_right h1, ite_eq_left hle]
    exact original_readback W hp z d hz
      (by omega)

end

end VaughtConjecture.Knight.GrowthHigherMixed
