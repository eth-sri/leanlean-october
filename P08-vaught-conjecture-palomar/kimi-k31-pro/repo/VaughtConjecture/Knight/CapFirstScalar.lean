/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourceBlockLocalityTransport
public import VaughtConjecture.Knight.AmbientGradeCharts

/-! # Preserve the output cap, not the old shifter's entire range

A relative lift needs capped prefix agreement only. Clipping the old normalized
witness at a visible output cap gives a canonical representative of that prefix.
A monotone replacement agreeing with the clipped prefix preserves all output caps
as soon as the old shifter reaches the output cap at the source cut. The source
cut and output cap are distinct parameters. No replacement member is constructed.
-/

@[expose] public section

namespace VaughtConjecture.Knight.CapFirstScalar

open Transform Value ExtOrd SharpWitnessComposition

/-- The old values above the output cap need not be retained literally. -/
theorem map_cap_agreement_of_capped_prefix {σ τ : ExtOrd → ExtOrd}
    (hσ : Monotone σ) (hτ : Monotone τ) {a x y γ : ExtOrd}
    (hprefix : ∀ z, z ≤ a → min (τ z) γ = min (σ z) γ)
    (hxy : min x a = min y a) (hactive : γ ≤ σ a) :
    min (τ x) γ = min (σ y) γ := by
  have hactive' : γ ≤ τ a := by
    have he := hprefix a le_rfl
    rw [min_eq_right hactive] at he
    exact (min_eq_right_iff.mp he)
  calc
    min (τ x) γ = min (τ (min x a)) γ := by
      rw [hτ.map_min, min_assoc, min_eq_right hactive']
    _ = min (σ (min x a)) γ := hprefix _ (min_le_right _ _)
    _ = min (σ (min y a)) γ := by rw [hxy]
    _ = min (σ y) γ := by
      rw [hσ.map_min, min_assoc, min_eq_right hactive]

/-- Keeping the clipped prefix is a sufficient, constructive form of capped agreement. -/
theorem map_cap_agreement_of_clipped_prefix {σ τ : ExtOrd → ExtOrd}
    (hσ : Monotone σ) (hτ : Monotone τ) {a x y γ : ExtOrd}
    (hprefix : ∀ z, z ≤ a → τ z = min (σ z) γ)
    (hxy : min x a = min y a) (hactive : γ ≤ σ a) :
    min (τ x) γ = min (σ y) γ := by
  apply map_cap_agreement_of_capped_prefix hσ hτ _ hxy hactive
  intro z hz
  rw [hprefix z hz, min_assoc, min_self]

