/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.OwnerwiseDecoding
import VaughtConjecture.Knight.GrowthPaddedCharts
import VaughtConjecture.Knight.GrowthGradeOneLift

/-! # Independent physical section supply on the padded grade-two carrier

Long inherited ladder rows are handled by their actual rank tables. Only the
new grade-two leaves use short-row composition. No positive-cap transport is
used to obtain bottom supply. The owner-by-owner argument is adapted from
LowOnlyPaddedSupply and uses the growth terminal decoder and boundary theorem.
-/

namespace VaughtConjecture.Knight.GrowthPaddedSupply
open     Growth
open GrowthPaddedSuccessor GrowthPaddedDecode GrowthPaddedCharts


variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "RespectsSemanticsBelow₀₀" => RespectsSemanticsBelow I.rows (A, 2)

local notation "input₀" => input I X T hA hB hC

theorem decoded_lower (a : Catalogue X 2) {δ}
    (hδ : Witness (gTop 2) δ)
    (hreflect : ∀ f, δ (a.val f) = ⊥ → a.val f = ⊥)
    (horiginal : RespectsSemanticsBelow₀₀
      (fun d => δ (a.val (GrowthOrderedBase.field I d.1)))) :
    RespectsSemanticsBelow (input₀).lowerRows (A, 2)
      (fun d => δ ((input₀).predecessor a d.1)) := by
  let J := input₀
  by_cases hz : δ J.ceiling = ⊥
  · have he (d) : δ (J.predecessor a d) = ⊥ :=
      le_bot_iff.mp ((hδ.mono (J.predecessor_bound a d)).trans_eq hz)
    change RespectsSemanticsBelow J.lowerRows (A, 2) (fun d => δ (J.predecessor a d.1))
    simp  [he]
    exact ⟨fun _ => (selfVis_bot).symm, fun c => by
      simpa only [min_self] using TransformsTo.to_bot,
      fun _ c _ _ => ⟨c, rfl, le_rfl⟩⟩
  · let f := fun i => δ (LadderScalarRendering.level
      (LadderScalarRendering.values (GrowthHigherSources.fields X 2 a)) J.ceiling i)
    apply RelativeLadderLayer.image_respects I.boundary I.rows J.one
      (GrowthOrderedBase.field I) (GrowthHigherSources.fields X 1)
      (GrowthOrderedBase.proper hB hC)
      (baseAnchor X a) f
      (hδ.mono.comp (LadderScalarRendering.level_mono
        (LadderScalarRendering.values_bound (J.bounded a))))
      (by simp  [f, LadderScalarRendering.level_zero, hδ.bot])
    · intro i
      have hv := LadderScalarRendering.level_visible (J.visible a)
        ((J.grid_visible _ J.ceiling_mem).mono (by decide)) i
      have he := hδ.clause5
        (LadderScalarRendering.level (LadderScalarRendering.values (J.upper a)) J.ceiling i)
        1 (by rw []; exact le_top) 1 le_rfl
      
      rw [hv] at he
      exact he.symm
    · intro i hi _
      have hp := LadderScalarRendering.level_pos
        (LadderScalarRendering.bot_not_values)
        (LadderScalarRendering.values_bound (J.bounded a))
        (fun h => hz (h ▸ hδ.bot)) hi
      rcases LadderScalarRendering.level_supported
          (LadderScalarRendering.values (GrowthHigherSources.fields X 2 a))
          J.ceiling i with he | he | he
      · exact (hp he).elim
      · obtain ⟨_, x, hx⟩ := LadderScalarRendering.mem_values.mp he
        intro h
        have hb := hreflect x ((congrArg δ hx).trans h)
        exact hp (hx.symm.trans hb)
      · exact fun h => hz (he ▸ h)
    · simpa only [f, baseAnchor_ranks, LadderScalarRendering.field_readback,
        ] using horiginal

local notation "RespectsSemanticsBelow₀" => RespectsSemanticsBelow (rows I X T hA hB hC)

local notation "carrier₀" => carrier I X T hA hB hC

local notation "old₀" => old I X T hA hB hC

/-- Retained proper owners can have grade two or higher. Separation, rather
than a false global predecessor grade bound, identifies their domains. -/
theorem old_respects_iff c
    p :
    RespectsSemanticsBelow₀
      ((carrier₀).cell (old₀ c)) p ↔
    RespectsSemanticsBelow (input₀).lowerRows
      ((input₀).lower.cell c)
      (p ∘ SeparatedSourceLayerCarrier.ownerEquiv (input₀).lower
        (LadderWeightedSuccessor.Input.Node (U := Catalogue X 2) (V := Empty))
        2 (by decide) hA (input₀).separation c) := by
  let J := input₀
  let e := SeparatedSourceLayerCarrier.ownerEquiv J.lower
    (LadderWeightedSuccessor.Input.Node (U := Catalogue X 2) (V := Empty))
    2 (by decide) hA J.separation c
  have hh := respects_iff_of_equiv e
    (fun d => (congrArg Prod.snd (SourceLayerCarrier.cell_toCell
      J.lower _ 2 (by decide) hA (.inl d.1))).symm)
    (fun d y => by simp only [e, CellScheme.scope,
      SeparatedSourceLayerCarrier.ownerEquiv_val, SourceLayerCarrier.cell_toCell,
      SourceLayerCarrier.index])
    (fun b d _ => (inherited_row I X T hA hB hC b.1 d).symm) (p ∘ e)
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using hh.symm

local notation "source₀" => source I X T hA hB hC

def decoded_lawful (a : Catalogue X 2) {δ}
    (hδ : Witness (gTop 2) δ)
    (hreflect : ∀ f, δ (a.val f) = ⊥ → a.val f = ⊥)
    (horiginal : RespectsSemanticsBelow₀₀
      (fun d => δ (a.val (GrowthOrderedBase.field I d.1)))) := by
  
  have hs := source_lawful I X T hA hB hC a
  have hl := decoded_lower I X T hA hB hC a hδ hreflect horiginal
  apply SharpWitnessComposition.map_respects_of_short_or_local hs (fun d => d.2.2) hδ
  intro c
  obtain ⟨x, hx⟩ | ⟨b, hb⟩ := GrowthPaddedSuccessor.cell_cases c.1
  · right
    have hxc  := by
      simpa only [hx, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index] using c.2
    have hp : RespectsSemanticsBelow₀
        ((carrier₀).cell (old₀ x))
        (fun d => δ (source₀ a d.1)) := by
      apply (old_respects_iff I X T hA hB hC x _).mpr
      simpa only [Function.comp_def, SeparatedSourceLayerCarrier.ownerEquiv_val,
        LadderWeightedSuccessor.Input.source_old, CellScheme.below.mono] using hl.mono hxc
    rcases c with ⟨c, hc⟩
    dsimp  at hx
    subst c
    exact hp.locality ⟨_, GradedLe.refl _⟩
  · left
    have hgrade : (carrier₀).grade c.1 = 2 := by
      rw [hb]; exact congrArg Prod.snd (leaf_index b)
    rw [hgrade, hb]
    intro d
    rw [leaf_row]
    exact source_short I X T hA hB hC b d.1

/-- Terminal insertion reflects bottom on every represented field. The long
rungs use the resulting rank table, not short-row composition. -/
theorem exists_section {S}
    (hS : Admitted X 2 S) :
    ∃ w, RespectsSemanticsBelow₀ (A, 2) w ∧
      ∀ d : I.boundary.below (A, 2),
        w ⟨original I X T hA hB hC d.1, by rw [original_index]; exact d.2⟩ =
          S.profile (GrowthOrderedBase.field I d.1) := by
  obtain ⟨Q, hQ, hcanon, δ, hδ, hread, hreflect, _⟩ :=
    Growth.exists_supported_decoder X (by decide : 1 ≤ 2) hS
  dsimp  [ Function.comp_def] at hread
  let a : Catalogue X 2 := ⟨Q.profile, hcanon, Q, hQ, rfl⟩
  have horiginal : RespectsSemanticsBelow₀₀
      (fun d => δ (a.val (GrowthOrderedBase.field I d.1))) := by
    simpa only [a, hread] using GrowthHigherSources.boundary_lawful_at I X T hS
  refine ⟨_, decoded_lawful I X T hA hB hC a hδ hreflect horiginal, ?_⟩
  intro d
  change δ (source₀ a (original I X T hA hB hC d.1)) = _
  rw [original_readback]
  exact hread _

/-- Independent bottom-cap private supply, allowing literal top. -/
theorem private_bottom_supply
    {p}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, 2) p) :
    ∃ w, RespectsSemanticsBelow₀ (A, 2) w ∧
      ∀ d, w (privateAt I X T hA hB hC d) = p d := by
  obtain ⟨S, hS, hr⟩ := T.private_bottom_state hp
  obtain ⟨w, hw, hread⟩ := exists_section I X T hA hB hC hS
  refine ⟨w, hw, fun d => ?_⟩
  have hd : GradedLe (I.boundary.cell (I.rightFace.map d.1)) (A, 2) := by
    refine ⟨I.boundary.scope_subset _, ?_⟩
    exact (congrArg Prod.snd (I.rightFace.index d.1)).le.trans d.2.2
  exact (hread ⟨_, hd⟩).trans
    ((GrowthOrderedBase.field_private T hS d.1).trans (hr d))

/-- Donor supply uses the pre-activation donor fibre, independently of any
positive-cap transport or symmetry assertion about growth admission. -/
theorem donor_bottom_supply (hN : 2 < X.req.N)
    {p}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, 2) p) :
    ∃ w, RespectsSemanticsBelow₀ (A, 2) w ∧
      ∀ d, w (donorAt I X T hA hB hC d) = p d := by
  obtain ⟨S, hS, hr⟩ := T.donor_bottom_state hN hp
  obtain ⟨w, hw, hread⟩ := exists_section I X T hA hB hC hS
  refine ⟨w, hw, fun d => ?_⟩
  have hd : GradedLe (I.boundary.cell (I.leftFace.map d.1)) (A, 2) := by
    refine ⟨I.boundary.scope_subset _, ?_⟩
    exact (congrArg Prod.snd (I.leftFace.index d.1)).le.trans d.2.2
  exact (hread ⟨_, hd⟩).trans ((GrowthOrderedBase.field_donor I).trans (hr d))


