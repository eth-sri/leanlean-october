/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OwnerwiseDecoding
public import VaughtConjecture.Knight.LowOnlyPaddedCharts
public import VaughtConjecture.Knight.LowOnlyDonorOrderedLift

/-! # Independent physical section supply on the padded grade-two carrier

Long inherited ladder rows are handled by their actual rank tables. Only the
new grade-two leaves use short-row composition. No positive-cap transport is
used to obtain bottom supply.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.LowOnlyPaddedSupply
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyPaddedSuccessor LowOnlyPaddedDecode LowOnlyPaddedCharts

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem decoded_lawful (a : F.Anchor 2) {δ : ExtOrd → ExtOrd}
    (hδ : Witness (gTop 2) δ)
    (hreflect : ∀ f, δ (a.val f) = ⊥ → a.val f = ⊥)
    (horiginal : RespectsSemanticsBelow I.rows (A, 2)
      (fun d => δ (a.val (LowOnlyOrderedLadder.field I d.1)))) :
    RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2)
      (fun d => δ (source I F hroot hA hB hC a d.1)) := by
  let J := input I F hroot hA hB hC
  have hl : RespectsSemanticsBelow J.lowerRows (A, 2) (fun d => δ (J.predecessor a d.1)) :=
    RelativeLadderLayer.renderWith_decode_respects I.boundary I.rows J.one
      (LowOnlyOrderedLadder.field I) (F.fields 1) (LowOnlyOrderedLadder.proper I hB hC)
      (by decide) (baseAnchor F a) (F.fields 2 a) (baseAnchor_ranks F a) (J.bounded a)
      (J.visible a) ((J.grid_visible _ J.ceiling_mem).mono (by decide)) hδ hreflect horiginal
  apply SharpWitnessComposition.map_respects_of_short_or_local
    (source_lawful I F hroot hA hB hC a) (fun d => d.2.2) hδ
  intro c
  obtain ⟨x, hx⟩ | ⟨b, hb⟩ := LowOnlyPaddedSuccessor.cell_cases I F hroot hA hB hC c.1
  · have hxc : GradedLe (J.lower.cell x) (A, 2) := by
      simpa only [hx, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index] using c.2
    have hp : RespectsSemanticsBelow (rows I F hroot hA hB hC)
        ((carrier I F hroot hA hB hC).cell (old I F hroot hA hB hC x))
        (fun d => δ (source I F hroot hA hB hC a d.1)) := by
      apply (WeightedSourcePrefixLayer.old_respects_iff J.data J.weight J.weight_visible
        (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ J.separation x)).mpr
      apply (SeparatedSourceLayerCarrier.base_respects_iff J.lower
        (LadderWeightedSuccessor.Input.Node (U := F.Anchor 2) (V := Empty))
        2 (by decide) hA J.separation J.lowerRows x _).mpr
      simpa only [Function.comp_def, SeparatedSourceLayerCarrier.ownerEquiv_val,
        LadderWeightedSuccessor.Input.source_old, CellScheme.below.mono] using hl.mono hxc
    rcases c with ⟨c, hc⟩; dsimp only at hx; subst c
    exact Or.inr (hp.locality ⟨_, GradedLe.refl _⟩)
  · left
    rw [show (carrier I F hroot hA hB hC).grade c.1 = 2 from
      hb ▸ congrArg Prod.snd (leaf_index I F hroot hA hB hC b), hb]
    intro d; rw [leaf_row]; exact source_short I F hroot hA hB hC b d.1

theorem exists_section {S : State I.left I.right} (hS : F.Admissible 2 S) :
    ∃ w, RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) w ∧
      ∀ d : I.boundary.below (A, 2),
        w ⟨original I F hroot hA hB hC d.1, by rw [original_index]; exact d.2⟩ =
          S.profile (LowOnlyOrderedLadder.field I d.1) := by
  obtain ⟨S₀, Q, _, _, hcap, hQeq, hQ, hcanon, δ, hδ, hread⟩ :=
    F.terminal_insertion (by decide : 1 ≤ 2) hS 0
  let a : F.Anchor 2 := ⟨Q.profile, hcanon, Q, hQ, rfl⟩
  have hreflect (f) (hf : δ (a.val f) = ⊥) : a.val f = ⊥ := by
    have he := State.capEq_iff_profile.mp hcap f
    rw [(hread f).symm.trans hf, min_bot_left] at he
    change Q.profile f = ⊥
    rw [hQeq, State.profile_normalize]
    exact (PairedSlotEncoding.normalize_bot_iff 2 S₀.profile f).mpr
      ((min_eq_bot.mp he).resolve_right (ofOrd_ne_bot 0))
  have horiginal : RespectsSemanticsBelow I.rows (A, 2)
      (fun d => δ (a.val (LowOnlyOrderedLadder.field I d.1))) := by
    simpa only [a, hread] using LowOnlyOrderedSources.boundary_lawful_at I F hroot 2 S hS
  refine ⟨_, decoded_lawful I F hroot hA hB hC a hδ hreflect horiginal, fun d => ?_⟩
  change δ (source I F hroot hA hB hC a (original I F hroot hA hB hC d.1)) = _
  rw [original_readback]; exact hread _

theorem private_bottom_supply
    {p : I.right.scheme.below (effC n 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (effC n 2) p) :
    ∃ w, RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) w ∧
      ∀ d, w (privateAt I F hroot hA hB hC d) = p d := by
  obtain ⟨S, hS, hr, _, _⟩ := F.private_bottom_supply hp
  obtain ⟨w, hw, hread⟩ := exists_section I F hroot hA hB hC hS
  refine ⟨w, hw, fun d => ?_⟩
  have hd : GradedLe (I.boundary.cell (I.rightFace.map d.1)) (A, 2) :=
    ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
      (congrArg Prod.snd (I.rightFace.index d.1)).le.trans (d.2.2.trans (min_le_left _ _))⟩
  exact (hread ⟨_, hd⟩).trans
    ((LowOnlyOrderedLadder.field_private I F hroot
      (LowOnlyRecursiveCoverage.admissible_down F (by decide) (by decide) hS) d.1).trans
      (congrFun hr d))

theorem donor_bottom_supply
    {p : I.left.scheme.below (effC n 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (effC n 2) p) :
    ∃ w, RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) w ∧
      ∀ d, w (donorAt I F hroot hA hB hC d) = p d := by
  obtain ⟨S, hS, hr, _, _⟩ := F.donor_bottom_supply hp
  obtain ⟨w, hw, hread⟩ := exists_section I F hroot hA hB hC hS
  refine ⟨w, hw, fun d => ?_⟩
  have hd : GradedLe (I.boundary.cell (I.leftFace.map d.1)) (A, 2) :=
    ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
      (congrArg Prod.snd (I.leftFace.index d.1)).le.trans (d.2.2.trans (min_le_left _ _))⟩
  exact (hread ⟨_, hd⟩).trans
    ((LowOnlyOrderedLadder.field_donor I S d.1).trans (congrFun hr d))
