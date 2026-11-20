/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SeparatedSourceLayerCarrier
public import VaughtConjecture.Knight.PairedSlotComparison
public import VaughtConjecture.Knight.CoatomBoundaryExtension

@[expose] public section

namespace VaughtConjecture.Knight.PairedCoupledSections

open Transform Value ExtOrd SourcePrefixRows SharpWitnessComposition

open PairedSlotEncoding PairedSlotComparison

noncomputable section

theorem short_replace {k i : ℕ} {x : ExtOrd} (hx : Short k x) (hi : i ≤ k) :
    Short k (extVisibilityReplace x k i) := by
  rcases hx with rfl | rfl | ⟨a, rfl, ha⟩
  · tauto
  · tauto
  · by_cases hk : finitePart a < k
    · rw [extVisibilityReplace_of_finitePart_lt hk]
      exact Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_limitPart_add_nat]; exact hi⟩)
    · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp hk)]
      tauto

theorem supported_short {X : Type*} {k : ℕ} {G : Finset ExtOrd} {p : X → ExtOrd}
    (hG : ∀ z ∈ G, Short k z) (hp : ∀ x, Short k (p x))
    {v : ExtOrd} (hv : OrbitPrefixSupport.Supported k (G : Set ExtOrd) p v) : Short k v := by
  rcases hv with rfl | hv | ⟨d, i, hi, rfl⟩
  · exact Or.inl rfl
  · exact hG _ hv
  · exact short_replace (hp d) hi

end

end VaughtConjecture.Knight.PairedCoupledSections
