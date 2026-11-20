/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutLayerCarrier

/-! # Literal row splice at a grade cut

Retain all proper boundary rows, including higher-grade and long rows. The
full-scope rows already constructed on the smaller grade cut are transported
across their exact lower domains; their source values are not renormalized.
-/

@[expose] public section

namespace VaughtConjecture.Knight.GradeCutLayerRows

open Transform Value ExtOrd SourceLayerCarrier GradeCutLayerCarrier
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (Q : Type*) [Fintype Q] (j : ℕ)
variable (hj : 0 < j) (hA : j ≤ A.card)
variable (hp : D.AvoidsScope A)
variable (sem : Semantics D) (low : Semantics (small D Q j hj hA))

variable (hmatch : ∀ (c : Cell (GradeCutBoundary.scheme D j))
  (d : (GradeCutBoundary.scheme D j).RowDomain c),
  low.E (toCell (GradeCutBoundary.scheme D j) Q j hj hA (.inl c))
    (ownerEquiv (GradeCutBoundary.scheme D j) Q j hj hA (GradeCutBoundary.proper D j hp) c d) =
  (GradeCutBoundary.rows D j sem).E c d)

include hmatch

omit hmatch in
theorem cast_respects {B C : Finset ι × ℕ} (h : B = C)
    {p : D.SectionAt B} (hr : sem.Lawful p) :
    RespectsSemanticsBelow sem C (fun d => p ⟨d.1, h.symm ▸ d.2⟩) := by
  subst C
  exact hr

end
end VaughtConjecture.Knight.GradeCutLayerRows
