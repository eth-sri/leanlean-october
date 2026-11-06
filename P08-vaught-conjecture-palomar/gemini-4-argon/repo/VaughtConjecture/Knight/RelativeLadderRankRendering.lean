/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RelativeLadderLayer

/-! # Rendering a new numerical table on a retained ladder anchor

Only field ranks are identified. The installed rows continue to use the birth
catalogue, while the rendered vector reads the incoming numerical values.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.RelativeLadderLayer
open Transform Value ExtOrd LadderScalarRendering

variable {ι X Q : Type*} [DecidableEq ι] [Fintype X] [Fintype Q] {A : Finset ι}
  (D : CellScheme A) (sem : Semantics D) (hA : 0 < A.card)
  (field : Cell D → X) (fields : Q → X → ExtOrd) (hp : ∀ d, D.scope d ≠ A)

def renderWith (a : Q) (p : X → ExtOrd) (C : ExtOrd) :
    Cell (carrier D hA (X := X) (Q := Q)) → ExtOrd :=
  image D hA field fields a (LadderScalarRendering.level (values p) C)

theorem renderWith_old (a : Q) (p : X → ExtOrd) (C : ExtOrd)
    (hr : ∀ x, ranks fields a x = fieldRank p x) (d : Cell D) :
    renderWith D hA field fields a p C (old D hA d) = p (field d) := by
  simp only [renderWith, image, rankIndex_old, hr, field_readback]

theorem renderWith_bound (a : Q) (p : X → ExtOrd) {C : ExtOrd}
    (hC : ∀ x, p x ≤ C) (d : Cell (carrier D hA (X := X) (Q := Q))) :
    renderWith D hA field fields a p C d ≤ C := level_le (values_bound hC) _

theorem renderWith_respects {j : ℕ} (a : Q) (p : X → ExtOrd) {C : ExtOrd}
    (hr : ∀ x, ranks fields a x = fieldRank p x)
    (hC : ∀ x, p x ≤ C) (hv : ∀ x, SelfVis 1 (p x)) (hvis : SelfVis 1 C)
    (ha : RespectsSemanticsBelow sem (A, j) (fun d => p (field d.1))) :
    RespectsSemanticsBelow (rows D sem hA field fields hp) (A, j)
      (fun d => renderWith D hA field fields a p C d.1) := by
  by_cases hz : C = ⊥
  · have he (d : Cell (carrier D hA (X := X) (Q := Q))) :
        renderWith D hA field fields a p C d = ⊥ :=
      le_bot_iff.mp ((renderWith_bound D hA field fields a p hC d).trans_eq hz)
    simp only [he]
    exact ⟨fun _ => (selfVis_bot _).symm, fun c => by
      simpa only [min_self] using TransformsTo.to_bot ((rows D sem hA field fields hp).E c.1),
      fun _ t _ _ => ⟨t, rfl, le_rfl⟩⟩
  · apply image_respects D sem hA field fields hp a _ (level_mono (values_bound hC))
      (level_zero _ _) (level_visible hv hvis)
      (fun _ hi _ => level_pos (bot_not_values _) (values_bound hC) hz hi)
    simpa only [hr, field_readback] using ha

theorem renderWith_decode_respects {j : ℕ} (hj : 1 ≤ j) (a : Q) (p : X → ExtOrd) {C : ExtOrd}
    (hr : ∀ x, ranks fields a x = fieldRank p x)
    (hC : ∀ x, p x ≤ C) (hv : ∀ x, SelfVis 1 (p x)) (hvis : SelfVis 1 C)
    {δ : ExtOrd → ExtOrd} (hδ : Witness (gTop j) δ)
    (hreflect : ∀ x, δ (p x) = ⊥ → p x = ⊥)
    (ha : RespectsSemanticsBelow sem (A, j) (fun d => δ (p (field d.1)))) :
    RespectsSemanticsBelow (rows D sem hA field fields hp) (A, j)
      (fun d => δ (renderWith D hA field fields a p C d.1)) := by
  by_cases hz : δ C = ⊥
  · have he (d) : δ (renderWith D hA field fields a p C d) = ⊥ :=
      le_bot_iff.mp ((hδ.mono (renderWith_bound D hA field fields a p hC d)).trans_eq hz)
    simp only [he]
    exact ⟨fun _ => (selfVis_bot _).symm, fun c => by
      simpa only [min_self] using TransformsTo.to_bot ((rows D sem hA field fields hp).E c.1),
      fun _ t _ _ => ⟨t, rfl, le_rfl⟩⟩
  · apply image_respects D sem hA field fields hp a (fun i => δ (LadderScalarRendering.level (values p) C i))
      (hδ.mono.comp (level_mono (values_bound hC)))
      (by simp only [level_zero, hδ.bot])
    · intro i
      have he := hδ.clause5 (LadderScalarRendering.level (values p) C i) 1
        (by rw [gTop_of_le hj]; exact le_top) 1 le_rfl
      change SelfVis 1 (δ _)
      rw [level_visible hv hvis i] at he
      exact he.symm
    · intro i hi _
      have hp' := level_pos (bot_not_values p) (values_bound hC) (fun h => hz (h ▸ hδ.bot)) hi
      rcases level_supported (values p) C i with he | he | he
      · exact (hp' he).elim
      · obtain ⟨_, x, hx⟩ := mem_values.mp he
        exact fun h => hp' (hx.symm.trans (hreflect x ((congrArg δ hx).trans h)))
      · exact fun h => hz (he ▸ h)
    · simpa only [hr, field_readback] using ha

theorem renderWith_agreement {a b : Q} {p q : X → ExtOrd} {C h : ExtOrd}
    (hra : ∀ x, ranks fields a x = fieldRank p x)
    (hrb : ∀ x, ranks fields b x = fieldRank q x)
    (ha : ∀ x, p x ≤ C) (hb : ∀ x, q x ≤ C) (hC : h ≤ C)
    (hag : ∀ x, min (p x) h = min (q x) h)
    (d : Cell (carrier D hA (X := X) (Q := Q))) :
    min (renderWith D hA field fields a p C d) h =
      min (renderWith D hA field fields b q C d) h := by
  rcases cell_cases D hA d with ⟨d, rfl⟩ | ⟨v, rfl⟩
  · rw [renderWith_old D hA field fields a p C hra,
      renderWith_old D hA field fields b q C hrb]; exact hag _
  · simpa only [renderWith, image, rankIndex_added, render, SupportLadderRows.image] using
      render_cap_agreement (L := rungs (X := X)) (ranks fields)
        (a := a) (b := b) le_rfl hra hrb ha hb hC hag v

theorem renderWith_supported (a : Q) (p : X → ExtOrd) (C : ExtOrd)
    (d : Cell (carrier D hA (X := X) (Q := Q))) :
    renderWith D hA field fields a p C d = ⊥ ∨
      (∃ x, renderWith D hA field fields a p C d = p x) ∨
      renderWith D hA field fields a p C d = C := by
  rcases level_supported (values p) C (rankIndex D hA field fields a d) with hz | hm | hc
  · exact Or.inl hz
  · obtain ⟨_, x, hx⟩ := mem_values.mp hm
    exact Or.inr (Or.inl ⟨x, hx.symm⟩)
  · exact Or.inr (Or.inr hc)
