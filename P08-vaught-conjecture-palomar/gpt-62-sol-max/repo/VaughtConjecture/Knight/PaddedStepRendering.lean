/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PaddedStepRows
public import VaughtConjecture.Knight.OwnerwiseDecoding
public import VaughtConjecture.Knight.RelativeLadderTableDecode

@[expose] public section

namespace VaughtConjecture.Knight.Padded.StepRendering

open Transform Value ExtOrd SourcePrefixRows SharpWitnessComposition

open PairedSlotComparison StepRows

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {K : Spec A} {k : ℕ}
  (P : Layer K k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

local notation "NextAnchor" => K.Anchor (k + 1)

abbrev baseMap (d : Cell (K.base)) := old P hnext (P.baseMap d)

theorem base_index (d : Cell (K.base)) :
    (carrier P hnext).cell (baseMap P hnext d) = K.base.cell d :=
  (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans (P.base_index d)

def sourceBirth (a : NextAnchor) : K.Anchor 1 :=
  P.birth (Nat.le_succ k) (K.state a) (K.state_admitted a) (K.state_proper a)

theorem sourceBirth_ranks (a : NextAnchor) (d : K.Field) :
    RelativeLadderLayer.ranks (K.fields 1) (sourceBirth P a) d =
      LadderScalarRendering.fieldRank (K.fields (k + 1) a) d := by
  rw [sourceBirth, P.birth_ranks, K.state_profile]

theorem source_base (a : NextAnchor) (d : Cell K.base) :
    source P hk hnext a (baseMap P hnext d) =
      RelativeLadderLayer.renderWith K.boundary K.one K.field (K.fields 1)
        (sourceBirth P a) (K.fields (k + 1) a) (ceiling P) d := by
  rw [baseMap, source_old]
  simpa [selected, sourceBirth, K.state_profile] using
    P.render_base (Nat.le_succ k) (K.state a) (K.state_admitted a) (K.state_proper a)
      (G := grid P) (H := ceiling P)
      (fun _ hz => (sourceGrid_visible hz).mono (Nat.le_succ k))
      ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
      (K.state_bound a) d

theorem base_row (c : Cell (K.base))
    (d : K.base.below (K.base.cell c)) :
    (rows P hk hnext).E (baseMap P hnext c)
      ⟨baseMap P hnext d.1, by simpa only [base_index] using d.2⟩ =
        K.baseRows.E c d :=
  (inherited_row P hk hnext (P.baseMap c)
    ⟨P.baseMap d.1, by simpa only [P.base_index] using d.2⟩).trans (P.base_row c d)

theorem base_respects (c : Cell (K.base))
    (p : Cell (carrier P hnext) → ExtOrd) :
    RespectsSemanticsBelow (rows P hk hnext) ((carrier P hnext).cell (baseMap P hnext c))
      (fun d => p d.1) ↔
      RespectsSemanticsBelow (K.baseRows)
        (K.base.cell c) (fun d => p (baseMap P hnext d.1)) :=
  (old_respects P hk hnext (P.baseMap c) p).trans
    (P.base_respects c (fun d => p (old P hnext d)))

include hk in
theorem cell_cases (d : Cell (carrier P hnext)) :
    (∃ c, d = baseMap P hnext c) ∨
      (carrier P hnext).scope d = A ∧ 2 ≤ (carrier P hnext).grade d ∧
        (carrier P hnext).grade d ≤ k + 1 := by
  obtain ⟨x, rfl⟩ := (SourceLayerCarrier.enumeration P.carrier NextAnchor
    (k + 1) (Nat.succ_pos k) hnext).surjective d
  rcases x with x | a
  · rcases P.cases x with ⟨c, rfl⟩ | ⟨hs, hl, hu⟩
    · exact Or.inl ⟨c, rfl⟩
    · have he := SourceLayerCarrier.cell_toCell P.carrier NextAnchor
        (k + 1) (Nat.succ_pos k) hnext (.inl x)
      exact Or.inr ⟨(congrArg Prod.fst he).trans hs,
        hl.trans_eq (congrArg Prod.snd he).symm,
        (congrArg Prod.snd he).le.trans (hu.trans (Nat.le_succ k))⟩
  · have he := SourceLayerCarrier.cell_toCell P.carrier NextAnchor
      (k + 1) (Nat.succ_pos k) hnext (.inr a)
    exact Or.inr ⟨congrArg Prod.fst he,
      (show 2 ≤ k + 1 by omega).trans_eq (congrArg Prod.snd he).symm,
      (congrArg Prod.snd he).le⟩

theorem higher_short (c : Cell (carrier P hnext)) (hc : (carrier P hnext).scope c = A)
    (hg : 2 ≤ (carrier P hnext).grade c)
    (d : (carrier P hnext).below ((carrier P hnext).cell c)) :
    Short ((carrier P hnext).grade c) ((rows P hk hnext).E c d) := by
  exact (attachment P hk hnext).higher_short 2 (source_short P hk hnext) P.higher_short c hc hg d

theorem source_ceiling_at (a : NextAnchor) (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k + 1) :
    ∃ c, (carrier P hnext).cell c = (A, i) ∧ source P hk hnext a c = ceiling P := by
  by_cases he : i = k + 1
  · subst i
    exact ⟨_, (controller P hnext a).2, ScopedSourcePrefixLayer.Data.profile_diagonal _ _⟩
  · obtain ⟨c, hc, hv⟩ := P.ceiling_at (Nat.le_succ k) (K.state a) (K.state_admitted a) (K.state_proper a)
      (G := grid P) (H := ceiling P) (fun _ hz => (sourceGrid_visible hz).mono (Nat.le_succ k))
      ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
      (K.state_bound a) i hi (by omega)
    exact ⟨old P hnext c, (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans hc,
      (source_old P hk hnext a c).trans hv⟩

end

end VaughtConjecture.Knight.Padded.StepRendering
