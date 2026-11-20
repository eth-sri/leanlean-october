/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthHigherMixedCharts
public import VaughtConjecture.Knight.GrowthMixedGradeOne

@[expose] public section

namespace VaughtConjecture.Knight.GrowthHigherMixed

open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources

open GrowthPaddedContract GrowthPaddedIteration SupportLadderRows LadderScalarRendering

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (G : GrowthPaddedIteration.BuildContext A B C R m n J)

local notation "P" => G.tower

local notation "D" => carrier G

local notation "Rows" => rows G

local notation "Fld" => Field G.I.right.scheme G.I.left.scheme

local notation "Pt" => RelativeLadderLayer.Point (X := Fld) (Q := Catalogue G.X 1)

local notation "ranks₁" => RelativeLadderLayer.ranks (fields G.X 1)

local notation "rungs" => RelativeLadderLayer.rungs (X := Fld)

variable {G} (W : Cut G)
  {p : CellScheme.below (carrier G) W.index → ExtOrd}

theorem ladder_lawful (hp : RespectsSemanticsBelow Rows W.index p) :
    SupportLadderRows.Lawful ranks₁
      (fun v => p (ladderAt W v)) := by
  exact GrowthMixedGradeOne.ladder_lawful W
    (hp.mono W.gradeOne)

namespace OwnerChart

variable {W} {c : Cell G.tower.carrier} (Ch : OwnerChart W p c)

local notation "O" => Ch.origin

set_option quotPrecheck false in
local notation "profile" => fields G.X ((O).birth + 2) (O).member
set_option quotPrecheck false in
local notation "render" => LadderScalarRendering.level (values profile) (O).ceiling

theorem ladder_read (v : Pt) : Ch.read (SupportLadderRows.image ranks₁ (O).anchor
    render v) = min (p (ladderAt W v)) (p Ch.point) := by
  simpa only [(O).row_ladder] using Ch.row (ladderAt W v) ((O).ladderArgument v) (erase_ladderAt W v)

/-- Reflection on every complete field, including hidden and future fields.
No global bottom-reflection property of the chart is asserted. -/
theorem bottom_reflection (hp : RespectsSemanticsBelow Rows W.index p)
    (hne : p Ch.point ≠ ⊥) (f : Fld) :
    Ch.read (profile f) = ⊥ → profile f = ⊥ := by
  have hceil := Ch.ceiling
  have hHne : (O).ceiling ≠ ⊥ := fun hz => by trivial
  have : Nonempty (Catalogue G.X 1) := ⟨GrowthLeafRecognition.zeroMember G.I G.X 1 le_rfl⟩
  have h0 : render 0 = ⊥ :=
    level_zero _ _
  have hf : ∀ i, 0 < i → i ≤ rungs →
      render i ≠ ⊥ :=
    fun i hi _ => level_pos (bot_not_values _) (values_bound (anchor_bound G.X (O).member)) hHne hi
  have hspare : Ch.read (render rungs) =
      p Ch.point := by
    have he := (O).row_ladder (SupportLadderRows.leaf (GrowthLeafRecognition.rungs_pos G.I) (O).anchor)
    rw [(O).row_spare] at he
    have hi := @SupportLadderRows.index_leaf Fld _ rungs ranks₁
      (GrowthLeafRecognition.rungs_pos G.I) (O).anchor (O).anchor
    have hu := hi.trans (FiniteProfileControllers.cut_refl _ _)
    exact (congrArg Ch.read ((congrArg render hu).symm.trans he.symm)).trans hceil
  have hr := Ch.ladder_read
  have hrefl := SupportLadderRows.bottom_reflection_image (GrowthLeafRecognition.rank_le_rungs G.I G.X)
    (GrowthLeafRecognition.rungs_pos G.I) (ladder_lawful W hp)
    (O).anchor h0 hf hne hr hspare (shadow (O).anchor f)
  have hidx := GrowthLeafRecognition.index_shadow_self G.I G.X (O).anchor f
  have har := GrowthPaddedNativeRows.anchor_ranks (O).birthContext (O).member f
  have hv : SupportLadderRows.image ranks₁ (O).anchor render (shadow (O).anchor f) = profile f :=
    (congrArg render (hidx.trans har)).trans (field_readback _ _ _)
  rw [← hv]
  exact hrefl.mp

end OwnerChart

/-- Admission of each grade-capped complete shadow vector is constructed from
the actual maximal owner's chart. There is no upward-admission step. -/
theorem exists_admitted_at (hp : RespectsSemanticsBelow Rows W.index p)
    (k : ℕ) (hk : 2 ≤ k) (hkj : k ≤ W.grade) :
    ∃ S : State G.I.right.scheme G.I.left.scheme, Admitted G.X k S ∧
      ∀ f, S.profile f = min (shadowSup W p f)
        (gradeMax W p k) := by
  by_cases hz : gradeMax W p k = ⊥
  · exact ⟨zero, zero_admitted G.X k, by aesop⟩
  obtain ⟨c, hc, hg, hmax⟩ := exists_maximal_owner W hp
    k (by omega) hkj
  obtain ⟨Ch⟩ := exists_owner_chart W hp c hc (hg.le.trans hkj) (hk.trans_eq hg.symm)
  let O := Ch.origin
  have hb : O.birth + 2 = k := (congrArg Prod.snd O.owner_index).symm.trans hg
  have hτ : Witness (gTop (O.birth + 2)) Ch.read := hb.symm ▸ (hg ▸ Ch.witness)
  refine ⟨(state G.X O.member).map Ch.read, hb ▸ ?_, fun f => ?_⟩
  · refine Admitted.map_on_profile G.X (state_admitted G.X O.member) hτ (by omega) fun f hf => ?_
    rw [state_profile] at hf ⊢
    exact Ch.bottom_reflection hp (fun he => hz (hmax.symm.trans he)) f hf
  · rw [State.profile_map, state_profile, ← hmax]
    exact Ch.recognition f

/-- Lawfulness on the entire original boundary, including originals absent
from the prescribed mixed scope, follows from the constructed admitted state. -/
theorem boundary_capped_lawful (hp : RespectsSemanticsBelow Rows W.index p)
    (k : ℕ) (hk : 2 ≤ k) (hkj : k ≤ W.grade) :
    RespectsSemanticsBelow G.I.rows (A, k) (fun d =>
      min (shadowSup W p (GrowthOrderedBase.field G.I d.1))
        (gradeMax W p k)) := by
  obtain ⟨S, hS, he⟩ := exists_admitted_at W hp k hk hkj
  have hl := GrowthOrderedBase.boundary_lawful G.I G.X G.attach hS
  grind

end

end VaughtConjecture.Knight.GrowthHigherMixed
