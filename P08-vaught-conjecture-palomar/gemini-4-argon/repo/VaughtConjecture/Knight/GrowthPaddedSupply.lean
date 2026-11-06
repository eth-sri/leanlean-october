/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OwnerwiseDecoding
public import VaughtConjecture.Knight.GrowthPaddedCharts
public import VaughtConjecture.Knight.GrowthGradeOneLift

/-! # Independent physical section supply on the padded grade-two carrier

Long inherited ladder rows are handled by their actual rank tables. Only the
new grade-two leaves use short-row composition. No positive-cap transport is
used to obtain bottom supply. The owner-by-owner argument is adapted from
LowOnlyPaddedSupply and uses the growth terminal decoder and boundary theorem.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.GrowthPaddedSupply
open Transform Value ExtOrd CappedDonor Growth GrowthPaddedSuccessor GrowthPaddedDecode GrowthPaddedCharts

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem exists_section {S : State I.right.scheme I.left.scheme}
    (hS : Admitted X 2 S) :
    ∃ w, RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) w ∧
      ∀ d : I.boundary.below (A, 2),
        w ⟨original I X T hA hB hC d.1, by rw [original_index]; exact d.2⟩ =
          S.profile (GrowthOrderedBase.field I d.1) := by
  obtain ⟨Q, hQ, hcanon, δ, hδ, hread, hreflect, _⟩ :=
    Growth.exists_supported_decoder X (by decide : 1 ≤ 2) hS
  let a : Catalogue X 2 := ⟨Q.profile, hcanon, Q, hQ, rfl⟩
  let J := input I X T hA hB hC
  have hl : RespectsSemanticsBelow J.lowerRows (A, 2) (fun d => δ (J.predecessor a d.1)) :=
    RelativeLadderLayer.renderWith_decode_respects I.boundary I.rows J.one
      (GrowthOrderedBase.field I) (GrowthHigherSources.fields X 1)
      (GrowthOrderedBase.proper I hB hC) (by decide) (baseAnchor X a)
      (GrowthHigherSources.fields X 2 a) (baseAnchor_ranks X a) (J.bounded a) (J.visible a)
      ((J.grid_visible _ J.ceiling_mem).mono (by decide)) hδ hreflect
      (by simpa only [a, hread] using GrowthHigherSources.boundary_lawful_at I X T hS)
  refine ⟨fun d => δ (source I X T hA hB hC a d.1),
    SharpWitnessComposition.map_respects_of_short_or_local
      (source_lawful I X T hA hB hC a) (fun d => d.2.2) hδ fun c => ?_,
    fun d => ?_⟩
  · obtain ⟨x, hx⟩ | ⟨b, hb⟩ := GrowthPaddedSuccessor.cell_cases I X T hA hB hC c.1
    · have hxc : GradedLe (J.lower.cell x) (A, 2) := by
        simpa only [hx, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index] using c.2
      have hp : RespectsSemanticsBelow (rows I X T hA hB hC)
          ((carrier I X T hA hB hC).cell (old I X T hA hB hC x))
          (fun d => δ (source I X T hA hB hC a d.1)) := by
        apply (WeightedSourcePrefixLayer.old_respects_iff J.data J.weight J.weight_visible
          (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ J.separation x)).mpr
        apply (SeparatedSourceLayerCarrier.base_respects_iff J.lower
          (LadderWeightedSuccessor.Input.Node (U := Catalogue X 2) (V := Empty))
          2 (by decide) hA J.separation J.lowerRows x _).mpr
        simpa only [Function.comp_def, SeparatedSourceLayerCarrier.ownerEquiv_val,
          LadderWeightedSuccessor.Input.source_old, CellScheme.below.mono] using hl.mono hxc
      rcases c with ⟨c, hc⟩; dsimp only at hx; subst c
      exact Or.inr (hp.locality ⟨_, GradedLe.refl _⟩)
    · left
      rw [show (carrier I X T hA hB hC).grade c.1 = 2 from
        hb ▸ congrArg Prod.snd (leaf_index I X T hA hB hC b), hb]
      intro d; rw [leaf_row]; exact source_short I X T hA hB hC b d.1
  · change δ (source I X T hA hB hC a (original I X T hA hB hC d.1)) = _
    rw [original_readback]; exact hread _

theorem private_bottom_supply
    {p : I.right.scheme.below (Finset.univ, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, 2) p) :
    ∃ w, RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) w ∧
      ∀ d, w (privateAt I X T hA hB hC d) = p d := by
  obtain ⟨S, hS, hr⟩ := T.private_bottom_state hp
  obtain ⟨w, hw, hread⟩ := exists_section I X T hA hB hC hS
  refine ⟨w, hw, fun d => ?_⟩
  have hd : GradedLe (I.boundary.cell (I.rightFace.map d.1)) (A, 2) :=
    ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
      (congrArg Prod.snd (I.rightFace.index d.1)).le.trans d.2.2⟩
  exact (hread ⟨_, hd⟩).trans
    ((GrowthOrderedBase.field_private I X T hS d.1).trans (hr d))

theorem donor_bottom_supply (hN : 2 < X.req.N)
    {p : I.left.scheme.below (Finset.univ, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, 2) p) :
    ∃ w, RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) w ∧
      ∀ d, w (donorAt I X T hA hB hC d) = p d := by
  obtain ⟨S, hS, hr⟩ := T.donor_bottom_state hN hp
  obtain ⟨w, hw, hread⟩ := exists_section I X T hA hB hC hS
  refine ⟨w, hw, fun d => ?_⟩
  have hd : GradedLe (I.boundary.cell (I.leftFace.map d.1)) (A, 2) :=
    ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
      (congrArg Prod.snd (I.leftFace.index d.1)).le.trans d.2.2⟩
  exact (hread ⟨_, hd⟩).trans ((GrowthOrderedBase.field_donor I S d.1).trans (hr d))
