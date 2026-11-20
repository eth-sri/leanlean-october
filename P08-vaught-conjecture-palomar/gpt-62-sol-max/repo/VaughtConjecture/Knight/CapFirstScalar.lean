/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourceBlockLocalityTransport
public import VaughtConjecture.Knight.AmbientGradeCharts

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
    grind
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
  aesop

end VaughtConjecture.Knight.CapFirstScalar
