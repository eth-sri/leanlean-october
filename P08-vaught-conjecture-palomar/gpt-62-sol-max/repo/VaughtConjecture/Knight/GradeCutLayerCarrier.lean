/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutBoundary

@[expose] public section

namespace VaughtConjecture.Knight.GradeCutLayerCarrier

open Transform Value ExtOrd

open SourceLayerCarrier

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

variable (D : CellScheme A) (Q : Type*) [Fintype Q] (j : ℕ)

variable (hj : 0 < j) (hA : j ≤ A.card)

abbrev small := scheme (GradeCutBoundary.scheme D j) Q j hj hA

abbrev enlarged := scheme D Q j hj hA

abbrev embed := appendMap Q j hj hA (GradeCutBoundary.toCell D j).toEmbedding

theorem embed_cell (d : Cell (small D Q j hj hA)) :
    (enlarged D Q j hj hA).cell (embed D Q j hj hA d) = (small D Q j hj hA).cell d :=
  appendMap_index Q j hj hA _ (fun _ => rfl) d

theorem exhaustive (d : Cell (enlarged D Q j hj hA))
    (hd : (enlarged D Q j hj hA).grade d ≤ j) : ∃ c, embed D Q j hj hA c = d :=
  appendMap_exhaustive Q j hj hA _ (fun _ => GradeCutBoundary.exhaustive D j) d hd

def belowEquiv (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ j) :
    (small D Q j hj hA).below BJ ≃ (enlarged D Q j hj hA).below BJ :=
  CellScheme.belowEquivOfIndex (embed D Q j hj hA) (embed D Q j hj hA).injective
    (embed_cell D Q j hj hA) (fun d hd => exhaustive D Q j hj hA d (hd.2.trans hBJ))

abbrev ownerEquiv (hp : ∀ d : Cell D, D.scope d ≠ A) (c : Cell D) :=
  SeparatedSourceLayerCarrier.ownerEquiv D Q j hj hA
    (SeparatedSourceLayerCarrier.separated_of_proper D j hp) c

def properEquiv (BJ : Finset ι × ℕ) (hB : ¬ A ⊆ BJ.1) :
    D.below BJ ≃ (enlarged D Q j hj hA).below BJ :=
  inheritedEquiv D Q j hj hA BJ (fun h => hB h.1)

end

end VaughtConjecture.Knight.GradeCutLayerCarrier
