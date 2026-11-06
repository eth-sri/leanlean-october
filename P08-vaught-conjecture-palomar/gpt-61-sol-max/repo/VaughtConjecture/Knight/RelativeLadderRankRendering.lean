
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.RelativeLadderLayer

/-! # Rendering a new numerical table on a retained ladder anchor

Only field ranks are identified. The installed rows continue to use the birth
catalogue, while the rendered vector reads the incoming numerical values.
-/

namespace VaughtConjecture.Knight.RelativeLadderLayer
open    LadderScalarRendering
noncomputable section
variable {ι X Q : Type*} [DecidableEq ι] [Fintype X] [Fintype Q] {A : Finset ι}
variable (D : CellScheme A) (sem : Semantics D) (hA : 0 < A.card)
  (field : Cell D → X) (fields : Q → X → ExtOrd) (hp : AvoidsValue D.scope A)

def renderWith (a : Q) (p : X → ExtOrd) (C : ExtOrd) :=
  image D hA field fields a (LadderScalarRendering.level (values p) C)

local notation "renderWith₀" => renderWith D hA field fields

variable {D fields} in
theorem renderWith_old {a : Q} {p : X → ExtOrd} {C : ExtOrd}
    (hr : ∀ x, ranks fields a x = fieldRank p x) {d : Cell D} :
    renderWith₀ a p C (old D hA d) = p (field d) := by
  simp  [renderWith, image,  hr, field_readback]

local notation "Cell₀" => Cell (carrier D hA (X := X) (Q := Q))

theorem renderWith_bound (a : Q) (p : X → ExtOrd) {C : ExtOrd}
    (hC : BoundedBy p C) (d : Cell₀) :
    renderWith₀ a p C d ≤ C := level_le (values_bound hC) _

theorem renderWith_respects {j} a p {C}
    (hr : ∀ x, ranks fields a x = fieldRank p x)
    (hC : BoundedBy p C) (hv : ∀ x, SelfVis 1 (p x)) (hvis : SelfVis 1 C)
    (ha : RespectsSemanticsBelow sem (A, j) (fun d => p (field d.1))) :
    RespectsSemanticsBelow (rows D sem hA field fields hp) (A, j)
      (fun d => renderWith₀ a p C d.1) := by
  by_cases hz : C = ⊥
  · have he (d : Cell₀) :
        renderWith₀ a p C d = ⊥ :=
      le_bot_iff.mp ((renderWith_bound D hA field fields a p hC d).trans_eq hz)
    simp  [he]
    exact ⟨fun _ => (selfVis_bot).symm, fun c => by
      simpa only [min_self] using TransformsTo.to_bot,
      fun _ t _ _ => ⟨t, rfl, le_rfl⟩⟩
  · apply image_respects D sem hA field fields hp a _ (level_mono (values_bound hC))
      (level_zero _ _) (level_visible hv hvis)
      (fun _ hi _ => level_pos (bot_not_values) (values_bound hC) hz hi)
    simpa only [hr, field_readback] using ha

/-- Agreement includes unused rungs and shadows of every retained anchor. -/
theorem renderWith_agreement {a b} {p q} {C h}
    (hra : ∀ x, ranks fields a x = fieldRank p x)
    (hrb : ∀ x, ranks fields b x = fieldRank q x)
    (ha : BoundedBy p C) (hb : BoundedBy q C) (hC : h ≤ C)
    (hag : CappedEq p q h)
    (d : Cell₀) :
    min (renderWith₀ a p C d) h =
      min (renderWith₀ b q C d) h := by
  rcases cell_cases d with ⟨d, rfl⟩ | ⟨v, rfl⟩
  · rw [renderWith_old hA field hra,
      renderWith_old hA field hrb]; exact hag _
  · have hh := render_cap_agreement  (ranks fields)
        le_rfl hra hrb ha hb hC hag v
    change min (LadderScalarRendering.level (values p) C
      (rankIndex D hA field fields a (added D hA v))) h = _
    rw [rankIndex_added]
    change min (LadderScalarRendering.level (values p) C
      (SupportLadderRows.index (ranks fields) a v)) h =
      min (LadderScalarRendering.level (values q) C
        (rankIndex D hA field fields b (added D hA v))) h
    rw [rankIndex_added]
    exact hh

theorem renderWith_supported {a : Q} {p : X → ExtOrd} {C : ExtOrd}
    (d : Cell₀) :
    renderWith₀ a p C d = ⊥ ∨
      (∃ x, renderWith₀ a p C d = p x) ∨
      renderWith₀ a p C d = C := by
  rcases level_supported (values p) C (rankIndex D hA field fields a d) with hz | hm | hc
  · exact Or.inl hz
  · obtain ⟨_, x, hx⟩ := mem_values.mp hm
    exact Or.inr (Or.inl ⟨x, hx.symm⟩)
  · exact Or.inr (Or.inr hc)

