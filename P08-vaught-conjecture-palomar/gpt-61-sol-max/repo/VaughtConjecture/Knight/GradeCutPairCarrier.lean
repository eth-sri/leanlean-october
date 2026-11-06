/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.GradeCutLayerCarrier

/-! # Retaining higher proper owners around two constructed lower layers

The same two controller inventories are installed over the cut boundary and
over the entire boundary. Their lower domains through the cut are identical.
No higher proper owner, lower controller, or occurrence is discarded.
-/

namespace VaughtConjecture.Knight.GradeCutPairCarrier
open    SourceLayerCarrier
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (Q R : Type*) [Fintype Q] [Fintype R]
variable (j k : ℕ) (hj : 0 < j) (hjA : j ≤ A.card) (hk : 0 < k) (hkA : k ≤ A.card)

abbrev lower := SourceLayerCarrier.scheme D Q j hj hjA
abbrev enlarged := SourceLayerCarrier.scheme (lower D Q j hj hjA) R k hk hkA
abbrev small := enlarged (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA

local notation "enlarged₀" => enlarged D Q R j k hj hjA hk hkA

def occEquiv : ((Cell D ⊕ Q) ⊕ R) ≃ Cell (enlarged₀) :=
  (Equiv.sumCongr (enumeration) (Equiv.refl R)).trans
    (enumeration)

local notation "occEquiv₀₀" => occEquiv D Q R j k hj hjA hk hkA

def cell x := occEquiv₀₀ x

def idx : (Cell D ⊕ Q) ⊕ R → GradedIndex ι
  | .inl (.inl d) => D.cell d
  | .inl (.inr _) => (A, j)
  | .inr _ => (A, k)

local notation "cell₀₀" => cell D Q R j k hj hjA hk hkA

theorem cell_idx x :
    (enlarged₀).cell (cell₀₀ x) =
      idx D Q R j k x := by
  rcases x with (d | q) | r
  · change (enlarged₀).cell
      (toCell _ R k hk hkA (.inl (toCell D Q j hj hjA (.inl d)))) = D.cell d
    simp only [cell_toCell, index]
  · change (enlarged₀).cell
      (toCell _ R k hk hkA (.inl (toCell D Q j hj hjA (.inr q)))) = (A, j)
    simp only [cell_toCell, index]
  · exact cell_toCell _ R k hk hkA (.inr r)

abbrev old d := cell₀₀ (.inl (.inl d))

local notation "occEquiv₀" => occEquiv (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA

local notation "small₀" => small D Q R j k hj hjA hk hkA

def embed d :=
  cell₀₀
    (Sum.map (Sum.map (GradeCutBoundary.toCell D k) id) id
      ((occEquiv₀).symm d))

local notation "cell₀" => cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA

local notation "embed₀" => embed D Q R j k hj hjA hk hkA

theorem embed_cell x :
    embed₀
      (cell₀ x) =
    cell₀₀ (Sum.map (Sum.map (GradeCutBoundary.toCell D k) id) id x) := by
  simp  [embed, cell, ]

variable {D Q R j k hj hjA hk hkA} in
theorem embed_index d :
    (enlarged₀).cell (embed₀ d) =
      (small₀).cell d := by
  obtain ⟨x, rfl⟩ := (occEquiv₀).surjective d
  change (enlarged₀).cell
    (embed₀ (cell _ _ _ _ _ _ _ _ _ x)) =
      (small₀).cell (cell _ _ _ _ _ _ _ _ _ x)
  rw [embed_cell, cell_idx, cell_idx]
  rcases x with (d | q) | r <;> rfl

theorem embed_injective : Function.Injective (embed₀) := by
  intro d e h
  apply (occEquiv₀).symm.injective
  exact (Sum.map_injective.mpr ⟨Sum.map_injective.mpr
    ⟨(GradeCutBoundary.toCell D k).injective, Function.injective_id⟩,
      Function.injective_id⟩) ((occEquiv₀₀).injective h)

theorem exhaustive d
    (hd : (enlarged₀).grade d ≤ k) :
    ∃ c, embed₀ c = d := by
  obtain ⟨x, rfl⟩ := (occEquiv₀₀).surjective d
  change (enlarged₀).grade (cell _ _ _ _ _ _ _ _ _ x) ≤ k at hd
  rw [CellScheme.grade, cell_idx] at hd
  rcases x with (d | q) | r
  · obtain ⟨c, hc⟩ := GradeCutBoundary.exhaustive D k hd
    refine ⟨cell₀ (.inl (.inl c)), ?_⟩
    rw [embed_cell]
    change cell _ _ _ _ _ _ _ _ _ (.inl (.inl (GradeCutBoundary.toCell D k c))) = _
    rw [hc]; rfl
  · exact ⟨cell₀ (.inl (.inr q)),
      embed_cell D Q R j k hj hjA hk hkA _⟩
  · exact ⟨cell₀ (.inr r),
      embed_cell D Q R j k hj hjA hk hkA _⟩

def belowEquiv (BJ : GradedIndex ι) (hBJ : BJ.2 ≤ k) :
    (small₀).below BJ ≃
      (enlarged₀).below BJ :=
  Equiv.ofBijective (fun d => ⟨embed₀ d.1, by
    simpa only [embed_index] using d.2⟩) ⟨by
      intro d e h
      exact Subtype.ext (embed_injective D Q R j k hj hjA hk hkA (congrArg Subtype.val h)), by
      intro d
      obtain ⟨c, hc⟩ := exhaustive D Q R j k hj hjA hk hkA d.1 (d.2.2.trans hBJ)
      refine ⟨⟨c, ?_⟩, Subtype.ext hc⟩
      simpa only [← embed_index c, hc] using d.2⟩

def properEquiv (BJ : GradedIndex ι) (hB : ¬ A ⊆ BJ.1) :
    D.below BJ ≃ (enlarged₀).below BJ :=
  (GradeCutLayerCarrier.properEquiv D Q j hj hjA BJ hB).trans
    (GradeCutLayerCarrier.properEquiv (lower D Q j hj hjA) R k hk hkA BJ hB)

theorem small_grade (hjk : j ≤ k) d :
    (small₀).grade d ≤ k := by
  obtain ⟨x, rfl⟩ := (occEquiv₀).surjective d
  change (small₀).grade (cell _ _ _ _ _ _ _ _ _ x) ≤ k
  rw [CellScheme.grade, cell_idx]
  rcases x with (d | q) | r
  · exact GradeCutBoundary.grade_bound d
  · exact hjk
  · exact le_rfl

