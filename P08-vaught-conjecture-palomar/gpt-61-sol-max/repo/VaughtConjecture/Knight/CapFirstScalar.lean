/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.SourceBlockLocalityTransport
import VaughtConjecture.Knight.AmbientGradeCharts

/-! # Preserve the output cap, not the old shifter's entire range

A relative lift needs capped prefix agreement only. Clipping the old normalized
witness at a visible output cap gives a canonical representative of that prefix.
A monotone replacement agreeing with the clipped prefix preserves all output caps
as soon as the old shifter reaches the output cap at the source cut. The source
cut and output cap are distinct parameters. No replacement member is constructed.
-/

namespace VaughtConjecture.Knight.CapFirstScalar


/-- The old values above the output cap need not be retained literally. -/
theorem map_cap_agreement_of_capped_prefix {σ τ : LabelMap}
    (hσ : Monotone σ) (hτ : Monotone τ) {a x y γ : ExtOrd}
    (hprefix : ∀ z, z ≤ a → min (τ z) γ = min (σ z) γ)
    (hxy : min x a = min y a) (hactive : γ ≤ σ a) :
    min (τ x) γ = min (σ y) γ := by
  have hactive' : γ ≤ τ a := by
    grind
  calc
    min (τ x) γ = min (τ (min x a)) γ := by
      rw [hτ.map_min, min_assoc, min_eq_right hactive']
    _ = min (σ (min x a)) γ := hprefix _ (min_le_right _ _)
    _ = min (σ (min y a)) γ := by rw [hxy]
    _ = min (σ y) γ := by
      rw [hσ.map_min, min_assoc, min_eq_right hactive]

/-- Keeping the clipped prefix is a sufficient, constructive form of capped agreement. -/
theorem map_cap_agreement_of_clipped_prefix {σ τ : LabelMap}
    (hσ : Monotone σ) (hτ : Monotone τ) {a x y γ : ExtOrd}
    (hprefix : ∀ z, z ≤ a → τ z = min (σ z) γ)
    (hxy : min x a = min y a) (hactive : γ ≤ σ a) :
    min (τ x) γ = min (σ y) γ := by aesop (add safe apply [map_cap_agreement_of_capped_prefix])

/-- A finite visible grid has a first point reaching a positive capped output. -/
theorem first_cut {k : ℕ} (G : Finset ExtOrd) {τ : LabelMap} {γ C : ExtOrd}
    (hbot : τ ⊥ = ⊥) (hb : γ ≠ ⊥) (hbound : BoundedBy τ γ) (hC : τ C = γ)
    (hmem : C ∈ G) (hvis : VisibleOn k G) (hmax : ∀ z ∈ G, z ≤ C) :
    ∃ h : ExtOrd, h ∈ G ∧ SelfVis k h ∧ ⊥ < h ∧ h ≤ C ∧
      τ h = γ ∧ ∀ z ∈ G, z < h → τ z < γ := by
  obtain ⟨h, hh, hmin⟩ := Finset.exists_min_image (G.filter fun h => γ ≤ τ h) id
    ⟨C, by simpa [hC] using hmem⟩
  simp only [Finset.mem_filter] at hh
  refine ⟨h, hh.1, hvis h hh.1, ?_, hmax h hh.1, le_antisymm (hbound h) hh.2, ?_⟩
  · apply bot_lt_iff_ne_bot.mpr
    intro hz
    exact hb (bot_unique (hh.2.trans_eq (hz ▸ hbot)))
  · intro z hz hzh
    exact lt_of_not_ge fun hn => (not_le_of_gt hzh) (hmin z (Finset.mem_filter.mpr ⟨hz, hn⟩))

