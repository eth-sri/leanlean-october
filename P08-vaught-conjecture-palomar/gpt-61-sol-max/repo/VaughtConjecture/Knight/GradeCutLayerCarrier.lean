
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GradeCutBoundary

/-! # Admitting higher proper owners alongside a constructed lower layer

The small carrier adds full-scope grade-j controllers to the grade-j boundary
cut. The enlarged carrier retains the entire original boundary and the very
same controller inventory. Its lower domains through j are exactly the small
carrier's, while every proper old owner's lower domain is exactly the old one.
-/

namespace VaughtConjecture.Knight.GradeCutLayerCarrier


open SourceLayerCarrier
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (Q : Type*) [Fintype Q] (j : ℕ)
variable (hj : 0 < j) (hA : j ≤ A.card)

abbrev small := scheme (GradeCutBoundary.scheme D j) Q j hj hA
abbrev enlarged := scheme D Q j hj hA

def embedOcc : Cell (GradeCutBoundary.scheme D j) ⊕ Q → Cell D ⊕ Q :=
  Sum.map (GradeCutBoundary.toCell D j) id

local notation "enlarged₀" => enlarged D Q j hj hA

local notation "small₀" => small D Q j hj hA

local notation "toCell₀" => toCell D Q j hj hA

def embed (d : Cell (small₀)) : Cell (enlarged₀) :=
  toCell₀ (embedOcc D Q j (toOcc (GradeCutBoundary.scheme D j) Q j hj hA d))

local notation "embed₀" => embed D Q j hj hA

local notation "toCell₀₀" => toCell (GradeCutBoundary.scheme D j) Q j hj hA

theorem embed_toCell x :
    embed₀ (toCell₀₀ x) =
      toCell₀ (embedOcc D Q j x) := by
  simp  [embed, ]

theorem embed_cell d :
    (enlarged₀).cell (embed₀ d) =
      (small₀).cell d := by
  rw [embed, cell_toCell, cell_eq]
  cases toOcc (GradeCutBoundary.scheme D j) Q j hj hA d <;> rfl

theorem embed_injective : Function.Injective (embed₀) := by
  intro d e h
  apply (enumeration).symm.injective
  have he := (enumeration).injective h
  
  exact (Sum.map_injective.mpr
    ⟨(GradeCutBoundary.toCell D j).injective, Function.injective_id⟩) he

theorem exhaustive d
    (hd : (enlarged₀).grade d ≤ j) : ∃ c, embed₀ c = d := by
  cases he : toOcc D Q j hj hA d with
  | inl c =>
    have hc  := by
      simpa only [CellScheme.grade, cell_eq, he, ] using hd
    obtain ⟨a, ha⟩ := GradeCutBoundary.exhaustive D j hc
    refine ⟨toCell₀₀ (.inl a), ?_⟩
    rw [embed_toCell]
    change toCell₀ (.inl (GradeCutBoundary.toCell D j a)) = d
    rw [ha, ← he, toCell_toOcc]
  | inr q =>
    refine ⟨toCell₀₀ (.inr q), ?_⟩
    rw [embed_toCell]
    change toCell₀ (.inr q) = d
    rw [← he, toCell_toOcc]

variable {Q j} in
variable {D hj hA} in
def belowEquiv (BJ : GradedIndex ι) (hBJ : BJ.2 ≤ j) :
    (small₀).below BJ ≃ (enlarged₀).below BJ :=
  Equiv.ofBijective (fun d => ⟨embed₀ d.1, by
    simpa only [embed_cell] using d.2⟩) ⟨by
      intro d e h
      exact Subtype.ext (embed_injective D Q j hj hA (congrArg Subtype.val h)), by
      intro d
      obtain ⟨c, hc⟩ := exhaustive D Q j hj hA d.1 (d.2.2.trans hBJ)
      refine ⟨⟨c, ?_⟩, Subtype.ext hc⟩
      simpa only [← embed_cell D Q j hj hA c, hc] using d.2⟩

variable {D Q j} in
abbrev ownerEquiv (hp : AvoidsValue D.scope A) c :=
  SeparatedSourceLayerCarrier.ownerEquiv D Q j hj hA
    (SeparatedSourceLayerCarrier.separated_of_proper D j hp) c

def properEquiv (BJ : GradedIndex ι) (hB : ¬ A ⊆ BJ.1) :
    D.below BJ ≃ (enlarged₀).below BJ :=
  Equiv.ofBijective (fun d => ⟨toCell₀ (.inl d.1), by
    simpa only [cell_toCell, index] using d.2⟩) ⟨by
      intro d e h
      exact Subtype.ext ((old_order).injective (congrArg Subtype.val h)), by
      intro d
      cases he : toOcc D Q j hj hA d.1 with
      | inl c =>
        have hc  := by
          simpa only [cell_eq, he, index] using d.2
        refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
        change toCell₀ (.inl c) = d.1
        rw [← he, toCell_toOcc]
      | inr q =>
        have hc  := by
          simpa only [CellScheme.scope, cell_eq, he, index] using d.2.1
        exact False.elim (hB hc)⟩

