/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.HighLayerBountiful
public import VaughtConjecture.Knight.ExactSemanticFace

@[expose] public section

namespace VaughtConjecture.Knight.SeparatedLayerFace

open Transform Value ExtOrd CoatomBoundaryExtension SourceLayerCarrier

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B : Finset ι}
  (D : CellScheme A) (Q : Type*) [Fintype Q] (k : ℕ) (hk : 0 < k) (hA : k ≤ A.card)
  (hs : ∀ d : Cell D, ¬ GradedLe (A, k) (D.cell d))
  (sem : Semantics D) (out : Semantics (scheme D Q k hk hA))
  (hrow : ∀ (c : Cell D) (d : D.below (D.cell c)),
    out.E (toCell D Q k hk hA (.inl c))
      (SeparatedSourceLayerCarrier.ownerEquiv D Q k hk hA hs c d) = sem.E c d)

def face {E : CellScheme B} {old : Semantics E}
    (F : ExactSemanticFace old sem) (hB : ¬ A ⊆ B) : ExactSemanticFace old out :=
  F.through ⟨fun d => toCell D Q k hk hA (.inl d), (old_order D Q k hk hA).injective⟩
    (fun d => cell_toCell D Q k hk hA (.inl d)) (fun z hz => by
      obtain ⟨c, hc⟩ := old_occurrence D Q k hk hA z (fun he => hB (by simpa only [CellScheme.scope, he] using hz))
      exact ⟨c, hc.symm⟩) hrow

end

end VaughtConjecture.Knight.SeparatedLayerFace
