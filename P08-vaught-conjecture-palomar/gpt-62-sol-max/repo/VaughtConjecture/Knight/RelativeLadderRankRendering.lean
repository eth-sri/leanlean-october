/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RelativeLadderLayer

@[expose] public section

namespace VaughtConjecture.Knight.RelativeLadderLayer

open Transform Value ExtOrd LadderScalarRendering

noncomputable section

variable {ι X Q : Type*} [DecidableEq ι] [Fintype X] [Fintype Q] {A : Finset ι}

variable (D : CellScheme A) (sem : Semantics D) (hA : 0 < A.card)
  (field : Cell D → X) (fields : Q → X → ExtOrd) (hp : ∀ d, D.scope d ≠ A)

def renderWith (a : Q) (p : X → ExtOrd) (C : ExtOrd) :
    Cell (carrier D hA (X := X) (Q := Q)) → ExtOrd :=
  image D hA field fields a (LadderScalarRendering.level (values p) C)

theorem renderWith_old (a : Q) (p : X → ExtOrd) (C : ExtOrd)
    (hr : ∀ x, ranks fields a x = fieldRank p x) (d : Cell D) :
    renderWith D hA field fields a p C (old D hA d) = p (field d) := by
  simp only [renderWith, image, rankIndex_old, hr, field_readback]

theorem renderWith_added (a : Q) (p : X → ExtOrd) (C : ExtOrd) (v : Point (X := X) (Q := Q)) :
    renderWith D hA field fields a p C (added D hA v) = render (ranks fields) a p C v := by
  simp only [renderWith, image, rankIndex_added, render, SupportLadderRows.image]

theorem renderWith_leaf (a : Q) (p : X → ExtOrd) (C : ExtOrd) :
    renderWith D hA field fields a p C (added D hA (SupportLadderRows.leaf (Nat.succ_pos _) a)) = C := by
  rw [renderWith_added, render, SupportLadderRows.image,
    SupportLadderRows.index_leaf (show 0 < rungs (X := X) from Nat.succ_pos _) a a,
    FiniteProfileControllers.cut_refl, level]
  exact ite_eq_left (Nat.lt_succ_of_le (values_card_le p))

theorem renderWith_bound (a : Q) (p : X → ExtOrd) {C : ExtOrd}
    (hC : ∀ x, p x ≤ C) (d : Cell (carrier D hA (X := X) (Q := Q))) :
    renderWith D hA field fields a p C d ≤ C := level_le (values_bound hC) _

theorem renderWith_map_respects {j : ℕ} (a : Q) (p : X → ExtOrd) {C : ExtOrd}
    (hr : ∀ x, ranks fields a x = fieldRank p x)
    (hC : ∀ x, p x ≤ C) (hv : ∀ x, SelfVis 1 (p x)) (hvis : SelfVis 1 C)
    {δ : ExtOrd → ExtOrd} (hmono : Monotone δ) (hbot : δ ⊥ = ⊥)
    (hvisδ : ∀ x, SelfVis 1 x → SelfVis 1 (δ x))
    (hreflect : ∀ x, δ (p x) = ⊥ → p x = ⊥)
    (ha : RespectsSemanticsBelow sem (A, j) (fun d => δ (p (field d.1)))) :
    RespectsSemanticsBelow (rows D sem hA field fields hp) (A, j)
      (fun d => δ (renderWith D hA field fields a p C d.1)) := by
  by_cases hz : δ C = ⊥
  · simpa only [show ∀ d, δ (renderWith D hA field fields a p C d) = ⊥ from
      fun d => le_bot_iff.mp ((hmono (renderWith_bound D hA field fields a p hC d)).trans_eq hz)]
      using RespectsSemanticsBelow.bot (rows D sem hA field fields hp) (A, j)
  · apply image_respects D sem hA field fields hp a (fun i => δ (level (values p) C i))
      (hmono.comp (level_mono (values_bound hC))) (by rw [level_zero, hbot])
      (fun i => hvisδ _ (level_visible hv hvis i))
    · intro i hi _ h
      have hpos := level_pos (bot_not_values p) (values_bound hC) (fun e => hz (e ▸ hbot)) hi
      rcases level_supported (values p) C i with e | hm | e
      · exact hpos e
      · obtain ⟨_, x, hx⟩ := mem_values.mp hm
        exact hpos (hx.symm.trans (hreflect x (hx ▸ h)))
      · exact hz (e ▸ h)
    · simpa only [hr, field_readback] using ha

theorem renderWith_respects {j : ℕ} (a : Q) (p : X → ExtOrd) {C : ExtOrd}
    (hr : ∀ x, ranks fields a x = fieldRank p x)
    (hC : ∀ x, p x ≤ C) (hv : ∀ x, SelfVis 1 (p x)) (hvis : SelfVis 1 C)
    (ha : RespectsSemanticsBelow sem (A, j) (fun d => p (field d.1))) :
    RespectsSemanticsBelow (rows D sem hA field fields hp) (A, j)
      (fun d => renderWith D hA field fields a p C d.1) :=
  renderWith_map_respects D sem hA field fields hp a p hr hC hv hvis
    (δ := id) monotone_id rfl (fun _ h => h) (fun _ h => h) ha

theorem renderWith_decode_respects {j : ℕ} (a : Q) (p : X → ExtOrd) {C : ExtOrd}
    (hr : ∀ x, ranks fields a x = fieldRank p x)
    (hC : ∀ x, p x ≤ C) (hv : ∀ x, SelfVis 1 (p x)) (hvis : SelfVis 1 C)
    {δ : ExtOrd → ExtOrd} (hj : 1 ≤ j) (hδ : Witness (gTop j) δ)
    (hreflect : ∀ x, δ (p x) = ⊥ → p x = ⊥)
    (ha : RespectsSemanticsBelow sem (A, j) (fun d => δ (p (field d.1)))) :
    RespectsSemanticsBelow (rows D sem hA field fields hp) (A, j)
      (fun d => δ (renderWith D hA field fields a p C d.1)) :=
  renderWith_map_respects D sem hA field fields hp a p hr hC hv hvis hδ.mono hδ.bot
    (fun x hx => by
      have h := hδ.comm x hj le_rfl
      rw [hx] at h
      exact h.symm) hreflect ha

/-- Agreement includes unused rungs and shadows of every retained anchor. -/
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
  · rw [renderWith_added, renderWith_added]
    exact render_cap_agreement (L := rungs (X := X)) (ranks fields) le_rfl hra hrb ha hb hC hag v

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

end

end VaughtConjecture.Knight.RelativeLadderLayer
