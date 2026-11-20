/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.HighLayerBountiful
public import VaughtConjecture.Knight.ExactSemanticFace

/-! # Literal face transport through a separated full-scope layer

Proper inherited owners may have grades above the added layer. Only separation
and literal rows are used; no global predecessor grade bound is imposed.
-/

@[expose] public section

namespace VaughtConjecture.Knight.SeparatedLayerFace
open Transform Value ExtOrd CoatomBoundaryExtension SourceLayerCarrier
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B : Finset ι}
  (D : CellScheme A) (Q : Type*) [Fintype Q] (k : ℕ) (hk : 0 < k) (hA : k ≤ A.card)
  (hs : ∀ d : Cell D, ¬ GradedLe (A, k) (D.cell d))
  (sem : Semantics D) (out : Semantics (scheme D Q k hk hA))
  (hrow : ∀ (c : Cell D) (d : D.RowDomain c),
    out.E (toCell D Q k hk hA (.inl c))
      (SeparatedSourceLayerCarrier.ownerEquiv D Q k hk hA hs c d) = sem.E c d)

def face {E : CellScheme B} {old : Semantics E}
    (F : ExactSemanticFace old sem) (hB : ¬ A ⊆ B) : ExactSemanticFace old out where
  map := F.map.trans ⟨fun d => toCell D Q k hk hA (.inl d),
    (old_order D Q k hk hA).injective⟩
  index d := (cell_toCell D Q k hk hA (.inl (F.map d))).trans (F.index d)
  exhaustive z hz := by
    obtain ⟨x, rfl⟩ := (enumeration D Q k hk hA).surjective z
    change ((scheme D Q k hk hA).cell (toCell D Q k hk hA x)).1 ⊆ B at hz
    rw [cell_toCell] at hz
    cases x with
    | inl d =>
      obtain ⟨e, rfl⟩ := F.exhaustive d hz
      exact ⟨e, rfl⟩
    | inr q => exact False.elim (hB hz)
  row c d := (hrow (F.map c) ⟨F.map d.1, by rw [F.index, F.index]; exact d.2⟩).trans
    (F.row c d)

end
end VaughtConjecture.Knight.SeparatedLayerFace
