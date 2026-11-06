/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedStepDecode
public import VaughtConjecture.Knight.OwnerwiseDecoding

/-! # Literal-top section supply on the recursive padded LOW rows

Terminal insertion supplies finite bottom reflection on the complete field
vector. The exact padded-base table then transports long-row lawfulness;
higher full-scope rows use short-row composition. No positive external cap,
predecessor lift or bountifulness of the new output is assumed.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.LowOnlyPaddedStepSupply
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder LowOnlyPaddedContract LowOnlyPaddedStepRows LowOnlyPaddedStepDecode
open LowOnlyPaddedStepRendering SharpWitnessComposition

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

def birth (a : F.Anchor (k + 1)) : F.Anchor 1 :=
  P.birth (Nat.le_succ k) (state F a) (state_admissible F a) (state_proper F a)

theorem birth_ranks (a : F.Anchor (k + 1)) (d : Field I.left I.right) :
    RelativeLadderLayer.ranks (F.fields 1) (birth P a) d =
      LadderScalarRendering.fieldRank (F.fields (k + 1) a) d := by
  rw [birth, P.birth_ranks, state_profile]

theorem source_base (a : F.Anchor (k + 1)) (d : Cell (base I F hroot hA hB hC)) :
    source P hk hnext a (baseMap P hnext d) =
      RelativeLadderLayer.renderWith I.boundary (by omega : 0 < A.card)
        (field I) (F.fields 1) (birth P a) (F.fields (k + 1) a) (ceiling P) d := by
  rw [baseMap, source_old]
  have he := P.render_base (Nat.le_succ k) (state F a) (state_admissible F a)
    (state_proper F a) (G := grid P) (H := ceiling P)
    (fun _ hz => (PairedSlotComparison.sourceGrid_visible hz).mono (Nat.le_succ k))
    ((PairedSlotComparison.sourceGrid_visible
      (PairedSlotComparison.sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
    (fun f => by rw [state_profile]; exact LowOnlyRecursiveCharts.anchor_bound F a f) d
  simpa only [selected, birth, state_profile] using he

theorem decoded_lawful (a : F.Anchor (k + 1)) {δ : ExtOrd → ExtOrd}
    (hδ : Witness (gTop (k + 1)) δ)
    (hreflect : ∀ f, δ (a.val f) = ⊥ → a.val f = ⊥)
    (horiginal : RespectsSemanticsBelow I.rows (A, k + 1)
      (fun d => δ (a.val (field I d.1)))) :
    RespectsSemanticsBelow (rows P hk hnext) (A, k + 1)
      (fun d => δ (source P hk hnext a d.1)) := by
  have hl : RespectsSemanticsBelow (baseRows I F hroot hA hB hC) (A, k + 1)
      (fun d => δ (source P hk hnext a (baseMap P hnext d.1))) := by
    simp only [source_base]
    exact RelativeLadderLayer.renderWith_decode_respects I.boundary I.rows (by omega)
      (field I) (F.fields 1) (proper I hB hC) (Nat.succ_pos k) (birth P a) (F.fields (k + 1) a)
      (birth_ranks P a) (LowOnlyRecursiveCharts.anchor_bound F a)
      (by simpa only [state_profile] using
        LowOnlyRecursiveCharts.profile_visible_one F (Nat.succ_pos k) (state_admissible F a))
      ((PairedSlotComparison.sourceGrid_visible
        (PairedSlotComparison.sourceGrid_endpoint le_rfl)).mono (Nat.succ_pos k))
      hδ hreflect horiginal
  apply map_respects_of_short_or_local (source_lawful P hk hnext a) (fun d => d.2.2) hδ
  intro c
  rcases LowOnlyPaddedStepRendering.cell_cases P hk hnext c.1 with
    ⟨b, he⟩ | ⟨hscope, hgrade, _⟩
  · have hb : GradedLe ((base I F hroot hA hB hC).cell b) (A, k + 1) := by
      simpa only [he, base_index] using c.2
    have hr := (base_respects P hk hnext b (fun d => δ (source P hk hnext a d))).mpr (hl.mono hb)
    rcases c with ⟨c, hc⟩; dsimp only at he; subst c
    exact Or.inr (hr.locality ⟨_, GradedLe.refl _⟩)
  · exact Or.inl (higher_short P hk hnext c.1 hscope hgrade)

theorem exists_section {S : State I.left I.right} (hS : F.Admissible (k + 1) S) :
    ∃ w, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) w ∧
      ∀ d : I.boundary.below (A, k + 1),
        w ⟨original P hnext d.1, by rw [original_index]; exact d.2⟩ =
          S.profile (field I d.1) := by
  obtain ⟨S₀, Q, _, _, hcap, hQeq, hQ, hcanon, δ, hδ, hread⟩ :=
    F.terminal_insertion (Nat.succ_pos k) hS 0
  let a : F.Anchor (k + 1) := ⟨Q.profile, hcanon, Q, hQ, rfl⟩
  have hreflect (f) (hf : δ (a.val f) = ⊥) : a.val f = ⊥ := by
    have he := State.capEq_iff_profile.mp hcap f
    rw [(hread f).symm.trans hf, min_bot_left] at he
    change Q.profile f = ⊥
    rw [hQeq, State.profile_normalize]
    exact (PairedSlotEncoding.normalize_bot_iff (k + 1) S₀.profile f).mpr
      ((min_eq_bot.mp he).resolve_right (ofOrd_ne_bot 0))
  have horiginal : RespectsSemanticsBelow I.rows (A, k + 1)
      (fun d => δ (a.val (field I d.1))) := by
    simpa only [a, hread] using LowOnlyOrderedSources.boundary_lawful_at I F hroot (k + 1) S hS
  refine ⟨_, decoded_lawful P hk hnext a hδ hreflect horiginal, fun d => ?_⟩
  change δ (source P hk hnext a (original P hnext d.1)) = _
  rw [source_original]; exact hread _

theorem private_bottom_supply
    {p : I.right.scheme.below (effC n (k + 1)) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (effC n (k + 1)) p) :
    ∃ w, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) w ∧
      ∀ d, w (privateAt P hnext d) = p d := by
  obtain ⟨S, hS, hr, _, _⟩ := F.private_bottom_supply hp
  obtain ⟨w, hw, hread⟩ := exists_section P hk hnext hS
  refine ⟨w, hw, fun d => ?_⟩
  have hd : GradedLe (I.boundary.cell (I.rightFace.map d.1)) (A, k + 1) :=
    ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
      (congrArg Prod.snd (I.rightFace.index d.1)).le.trans (d.2.2.trans (min_le_left _ _))⟩
  exact (hread ⟨_, hd⟩).trans
    ((field_private I F hroot
      (LowOnlyRecursiveCoverage.admissible_down F (by omega) (by omega) hS) d.1).trans
      (congrFun hr d))

theorem donor_bottom_supply
    {p : I.left.scheme.below (effC n (k + 1)) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (effC n (k + 1)) p) :
    ∃ w, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) w ∧
      ∀ d, w (donorAt P hnext d) = p d := by
  obtain ⟨S, hS, hr, _, _⟩ := F.donor_bottom_supply hp
  obtain ⟨w, hw, hread⟩ := exists_section P hk hnext hS
  refine ⟨w, hw, fun d => ?_⟩
  have hd : GradedLe (I.boundary.cell (I.leftFace.map d.1)) (A, k + 1) :=
    ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
      (congrArg Prod.snd (I.leftFace.index d.1)).le.trans (d.2.2.trans (min_le_left _ _))⟩
  exact (hread ⟨_, hd⟩).trans ((field_read I S (I.leftFace.map d.1)).trans
    ((I.paste_left S.u S.v d.1).trans (congrFun hr d)))
