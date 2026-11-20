/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutLayerCarrier

@[expose] public section

namespace VaughtConjecture.Knight.GradeCutPairCarrier

open Transform Value ExtOrd SourceLayerCarrier

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

variable (D : CellScheme A) (Q R : Type*) [Fintype Q] [Fintype R]

variable (j k : ℕ) (hj : 0 < j) (hjA : j ≤ A.card) (hk : 0 < k) (hkA : k ≤ A.card)

abbrev lower := SourceLayerCarrier.scheme D Q j hj hjA

abbrev enlarged := SourceLayerCarrier.scheme (lower D Q j hj hjA) R k hk hkA

abbrev small := enlarged (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA

def occEquiv : ((Cell D ⊕ Q) ⊕ R) ≃ Cell (enlarged D Q R j k hj hjA hk hkA) :=
  (Equiv.sumCongr (enumeration D Q j hj hjA) (Equiv.refl R)).trans
    (enumeration (lower D Q j hj hjA) R k hk hkA)

def cell (x : (Cell D ⊕ Q) ⊕ R) := occEquiv D Q R j k hj hjA hk hkA x

def idx : (Cell D ⊕ Q) ⊕ R → Finset ι × ℕ
  | .inl (.inl d) => D.cell d
  | .inl (.inr _) => (A, j)
  | .inr _ => (A, k)

theorem cell_idx (x : (Cell D ⊕ Q) ⊕ R) :
    (enlarged D Q R j k hj hjA hk hkA).cell (cell D Q R j k hj hjA hk hkA x) =
      idx D Q R j k x := by
  rcases x with (d | q) | r
  · change (enlarged D Q R j k hj hjA hk hkA).cell
      (toCell _ R k hk hkA (.inl (toCell D Q j hj hjA (.inl d)))) = D.cell d
    simp only [cell_toCell, index]
  · change (enlarged D Q R j k hj hjA hk hkA).cell
      (toCell _ R k hk hkA (.inl (toCell D Q j hj hjA (.inr q)))) = (A, j)
    simp only [cell_toCell, index]
  · exact cell_toCell _ R k hk hkA (.inr r)

abbrev old (d : Cell D) := cell D Q R j k hj hjA hk hkA (.inl (.inl d))

abbrev embed := appendMap R k hk hkA
  (appendMap Q j hj hjA (GradeCutBoundary.toCell D k).toEmbedding)

theorem embed_index (d : Cell (small D Q R j k hj hjA hk hkA)) :
    (enlarged D Q R j k hj hjA hk hkA).cell (embed D Q R j k hj hjA hk hkA d) =
      (small D Q R j k hj hjA hk hkA).cell d :=
  appendMap_index R k hk hkA _ (appendMap_index Q j hj hjA _ (fun _ => rfl)) d

theorem exhaustive (d : Cell (enlarged D Q R j k hj hjA hk hkA))
    (hd : (enlarged D Q R j k hj hjA hk hkA).grade d ≤ k) :
    ∃ c, embed D Q R j k hj hjA hk hkA c = d :=
  appendMap_exhaustive R k hk hkA _
    (appendMap_exhaustive Q j hj hjA _ (fun _ => GradeCutBoundary.exhaustive D k)) d hd

def belowEquiv (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ k) :
    (small D Q R j k hj hjA hk hkA).below BJ ≃
      (enlarged D Q R j k hj hjA hk hkA).below BJ :=
  CellScheme.belowEquivOfIndex (embed D Q R j k hj hjA hk hkA) (embed D Q R j k hj hjA hk hkA).injective
    (embed_index D Q R j k hj hjA hk hkA) (fun d hd => exhaustive D Q R j k hj hjA hk hkA d (hd.2.trans hBJ))

def properEquiv (BJ : Finset ι × ℕ) (hB : ¬ A ⊆ BJ.1) :
    D.below BJ ≃ (enlarged D Q R j k hj hjA hk hkA).below BJ :=
  (GradeCutLayerCarrier.properEquiv D Q j hj hjA BJ hB).trans
    (GradeCutLayerCarrier.properEquiv (lower D Q j hj hjA) R k hk hkA BJ hB)

theorem small_grade (hjk : j ≤ k) (d : Cell (small D Q R j k hj hjA hk hkA)) :
    (small D Q R j k hj hjA hk hkA).grade d ≤ k :=
  grade_bound _ R k hk hkA (grade_bound _ Q j hj hjA (GradeCutBoundary.grade_bound D k) hjk) le_rfl d

end

end VaughtConjecture.Knight.GradeCutPairCarrier
