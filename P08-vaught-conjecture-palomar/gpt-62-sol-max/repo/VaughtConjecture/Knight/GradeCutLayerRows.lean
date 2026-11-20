/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutLayerCarrier
public import VaughtConjecture.Knight.GradeCutAssembly

@[expose] public section

namespace VaughtConjecture.Knight.GradeCutLayerRows

open Transform Value ExtOrd SourceLayerCarrier GradeCutLayerCarrier

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

variable (D : CellScheme A) (Q : Type*) [Fintype Q] (j : ℕ)

variable (hj : 0 < j) (hA : j ≤ A.card)

variable (hp : ∀ d : Cell D, D.scope d ≠ A)

variable (sem : Semantics D) (low : Semantics (small D Q j hj hA))

include hp in
theorem proper_scope (c : Cell D) : ¬ A ⊆ D.scope c := by
  intro hc
  exact hp c (Finset.Subset.antisymm (D.scope_subset c) hc)

abbrev assembly := (GradeCutAssembly.initial D j hp).append Q j hj hA le_rfl

abbrev rows := (assembly D Q j hj hA hp).rows sem low

theorem old_row (c : Cell D) (d : D.below (D.cell c)) :
    (rows D Q j hj hA hp sem low).E (toCell D Q j hj hA (.inl c))
      (ownerEquiv D Q j hj hA hp c d) = sem.E c d :=
  (assembly D Q j hj hA hp).union.old_row sem low c d

theorem old_respects_iff (c : Cell D)
    (p : (enlarged D Q j hj hA).below
      ((enlarged D Q j hj hA).cell (toCell D Q j hj hA (.inl c))) → ExtOrd) :
    RespectsSemanticsBelow (rows D Q j hj hA hp sem low) _ p ↔
      RespectsSemanticsBelow sem (D.cell c) (p ∘ ownerEquiv D Q j hj hA hp c) :=
  iff_comp_symm (ownerEquiv D Q j hj hA hp c).symm
    (fun r => respects_iff_of_index_equiv (ownerEquiv D Q j hj hA hp c)
      (fun d => cell_toCell D Q j hj hA (.inl d.1))
      (fun b d _ => (old_row D Q j hj hA hp sem low b.1 d).symm) r) p

variable (hmatch : ∀ (c : Cell (GradeCutBoundary.scheme D j))
  (d : (GradeCutBoundary.scheme D j).below ((GradeCutBoundary.scheme D j).cell c)),
  low.E (toCell (GradeCutBoundary.scheme D j) Q j hj hA (.inl c))
    (ownerEquiv (GradeCutBoundary.scheme D j) Q j hj hA (GradeCutBoundary.proper D j hp) c d) =
  (GradeCutBoundary.rows D j sem).E c d)

include hmatch

theorem embedded_row (c : Cell (small D Q j hj hA))
    (d : (small D Q j hj hA).below ((small D Q j hj hA).cell c)) :
    (rows D Q j hj hA hp sem low).E (embed D Q j hj hA c)
      ⟨embed D Q j hj hA d.1, by grind [embed_cell]⟩ = low.E c d :=
  (assembly D Q j hj hA hp).union.low_row sem low
    ((assembly D Q j hj hA hp).agreement sem low hmatch) c d

theorem lower_respects_iff (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ j)
    (p : (small D Q j hj hA).below BJ → ExtOrd) :
    RespectsSemanticsBelow low BJ p ↔
      RespectsSemanticsBelow (rows D Q j hj hA hp sem low) BJ
        (p ∘ (belowEquiv D Q j hj hA BJ hBJ).symm) :=
  (assembly D Q j hj hA hp).cut_respects_iff hmatch BJ hBJ p

omit hmatch in
theorem cast_respects {B C : Finset ι × ℕ} (h : B = C)
    {p : D.below B → ExtOrd} (hr : RespectsSemanticsBelow sem B p) :
    RespectsSemanticsBelow sem C (fun d => p ⟨d.1, h.symm ▸ d.2⟩) := hr.castIndex h

theorem consistent (hs : sem.IsConsistent) (hl : low.IsConsistent) :
    (rows D Q j hj hA hp sem low).IsConsistent :=
  (assembly D Q j hj hA hp).union.consistent sem low
    ((assembly D Q j hj hA hp).agreement sem low hmatch) hs hl

end

end VaughtConjecture.Knight.GradeCutLayerRows
