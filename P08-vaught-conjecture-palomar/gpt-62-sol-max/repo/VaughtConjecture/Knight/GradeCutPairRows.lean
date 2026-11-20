/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutPairCarrier
public import VaughtConjecture.Knight.GradeCutLayerRows

@[expose] public section

namespace VaughtConjecture.Knight.GradeCutPairRows

open Transform Value ExtOrd GradeCutPairCarrier

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

variable (D : CellScheme A) (Q R : Type*) [Fintype Q] [Fintype R]

variable (j k : ℕ) (hj : 0 < j) (hjA : j ≤ A.card) (hk : 0 < k) (hkA : k ≤ A.card)

variable (hp : ∀ d : Cell D, D.scope d ≠ A) (hjk : j ≤ k)

variable (sem : Semantics D) (low : Semantics (small D Q R j k hj hjA hk hkA))

def ownerEquiv (c : Cell D) :=
  properEquiv D Q R j k hj hjA hk hkA (D.cell c) (GradeCutLayerRows.proper_scope D hp c)

abbrev assembly := ((GradeCutAssembly.initial D k hp).append Q j hj hjA hjk).append R k hk hkA le_rfl

abbrev rows := (assembly D Q R j k hj hjA hk hkA hp hjk).rows sem low

theorem old_row (c : Cell D) (d : D.below (D.cell c)) :
    (rows D Q R j k hj hjA hk hkA hp hjk sem low).E
      (old D Q R j k hj hjA hk hkA c)
      ⟨(ownerEquiv D Q R j k hj hjA hk hkA hp c d).1, by
        simpa only [old, cell_idx, GradeCutPairCarrier.idx] using
          (ownerEquiv D Q R j k hj hjA hk hkA hp c d).2⟩ =
    sem.E c d :=
  (assembly D Q R j k hj hjA hk hkA hp hjk).union.old_row sem low c d

variable (hmatch : ∀ (c : Cell (GradeCutBoundary.scheme D k))
    (d : (GradeCutBoundary.scheme D k).below ((GradeCutBoundary.scheme D k).cell c)),
    low.E (old (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA c)
      ⟨old (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA d.1, by
        simpa only [old, cell_idx, GradeCutPairCarrier.idx] using d.2⟩ =
      (GradeCutBoundary.rows D k sem).E c d)

include hmatch in
theorem embedded_row (c : Cell (small D Q R j k hj hjA hk hkA))
    (d : (small D Q R j k hj hjA hk hkA).below
      ((small D Q R j k hj hjA hk hkA).cell c)) :
    (rows D Q R j k hj hjA hk hkA hp hjk sem low).E (embed D Q R j k hj hjA hk hkA c)
      ⟨embed D Q R j k hj hjA hk hkA d.1, by simpa only [embed_index] using d.2⟩ = low.E c d :=
  (assembly D Q R j k hj hjA hk hkA hp hjk).union.low_row sem low
    ((assembly D Q R j k hj hjA hk hkA hp hjk).agreement sem low hmatch) c d

include hmatch in
theorem lower_respects_iff (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ k)
    (p : (small D Q R j k hj hjA hk hkA).below BJ → ExtOrd) :
    RespectsSemanticsBelow low BJ p ↔
      RespectsSemanticsBelow (rows D Q R j k hj hjA hk hkA hp hjk sem low) BJ
        (p ∘ (belowEquiv D Q R j k hj hjA hk hkA BJ hBJ).symm) :=
  (assembly D Q R j k hj hjA hk hkA hp hjk).cut_respects_iff hmatch BJ hBJ p

include hmatch in
theorem consistent (hs : sem.IsConsistent) (hl : low.IsConsistent) :
    (rows D Q R j k hj hjA hk hkA hp hjk sem low).IsConsistent :=
  (assembly D Q R j k hj hjA hk hkA hp hjk).union.consistent sem low
    ((assembly D Q R j k hj hjA hk hkA hp hjk).agreement sem low hmatch) hs hl

end

end VaughtConjecture.Knight.GradeCutPairRows
