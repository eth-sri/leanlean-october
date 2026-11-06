/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PairedBoundarySections

/-! # Coupling paired controller layers on their actual carriers

The upper source family remains indexed by the original proper boundary.
Its readings at every lower controller are constructed by the lower paired
section operator. No lower-section existence, agreement or future locality
hypothesis is supplied. Both original long rows and the lower controller rows
remain literal. This is a two-layer construction, not arbitrary-ambient lifting.
-/

@[expose] public section

namespace VaughtConjecture.Knight.PairedCoupledSections

open Transform Value ExtOrd SourcePrefixRows SharpWitnessComposition
open PairedSlotEncoding PairedSlotComparison

noncomputable section

theorem short_replace {k i} {x} (hx : Short k x) (hi : i ≤ k) :
    Short k (extVisibilityReplace x k i) := by
  rcases hx with rfl | rfl | ⟨a, rfl, ha⟩
  · exact Or.inl (extVisibilityReplace_bot _ _)
  · exact Or.inr (Or.inl (extVisibilityReplace_top _ _))
  · by_cases hk : finitePart a < k
    · rw [extVisibilityReplace_of_finitePart_lt hk]
      exact Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_limitPart_add_nat]; exact hi⟩)
    · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp hk)]
      exact Or.inr (Or.inr ⟨a, rfl, ha⟩)

theorem supported_short {X} {k} {G : Finset ExtOrd} {p : X → ExtOrd}
    (hG : ∀ z ∈ G, Short k z) (hp : ∀ x, Short k (p x))
    {v} (hv : OrbitPrefixSupport.Supported k (G : Set ExtOrd) p v) : Short k v := by
  rcases hv with rfl | hv | ⟨d, i, hi, rfl⟩
  · exact Or.inl rfl
  · exact hG _ hv
  · exact short_replace (hp d) hi

end
end VaughtConjecture.Knight.PairedCoupledSections
