/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OwnerLocalAlignment
public import VaughtConjecture.Knight.CanonicalPairedInverse

/-! # Private-row factorization with frozen source receipts

This adapter concerns an actual original owner's lower domain. It constructs
the lawful replacement section and its bounded outgoing witness from the old
source and actual prescribed lawfulness. It does not install a receiving
catalogue or assume that arbitrary physical sections are source states.
-/

@[expose] public section

namespace VaughtConjecture.Knight.PrivateRowFactorization
open Transform Value ExtOrd SharpWitnessComposition OwnerLocalEndpoint
noncomputable section

theorem coded_proper {m j : ℕ} {x : ExtOrd} (hx : x ∈ ExtOrd.codedAlphabet m j) :
    x ≠ ⊤ := by
  rcases ExtOrd.mem_codedAlphabet_iff.mp hx with rfl | ⟨b, i, _, _, rfl⟩
  · exact bot_ne_top
  · exact ofOrd_ne_top _

theorem code_spec {m j : ℕ} {x : ExtOrd}
    (hc : x ∈ ExtOrd.codedAlphabet m j) (hs : Short j x) :
    x = ⊥ ∨ ∃ b i : ℕ, b ≤ m ∧ i ≤ j ∧ x = ofOrd (Ordinal.omega0 * b + i) := by
  rcases ExtOrd.mem_codedAlphabet_iff.mp hc with hb | ⟨b, i, hb, _, he⟩
  · exact Or.inl hb
  · refine Or.inr ⟨b, i, hb, ?_, he⟩
    rcases hs with hz | ht | ⟨u, hu, hj⟩
    · exact (ofOrd_ne_bot _ (he.symm.trans hz)).elim
    · exact (ofOrd_ne_top _ (he.symm.trans ht)).elim
    have heq := ofOrd_inj.mp (he.symm.trans hu)
    simpa only [← heq, finitePart_mul_add] using hj

theorem endpoint_grid {m j : ℕ} {x : ExtOrd}
    (hc : x ∈ ExtOrd.codedAlphabet m j) (hs : Short j x) (h : ⊥ < endpoint j x) :
    ∃ b ≤ m, endpoint j x = CanonicalPairedInverse.grid j b := by
  rcases code_spec hc hs with rfl | ⟨b,i,hb,hi,rfl⟩
  · exact (lt_irrefl _ h).elim
  refine ⟨b,hb,?_⟩
  rcases lt_or_eq_of_le hi with hl | rfl
  · rw [endpoint, extVisibilityReplace_of_finitePart_lt (by rwa [finitePart_mul_add]),limitPart_mul_add]; rfl
  · apply endpoint_of_selfVis
    exact CanonicalPairedInverse.grid_visible _ b

theorem short_replace {j k i : ℕ} {x : ExtOrd} (hx : Short j x)
    (hk : k ≤ j) (hi : i ≤ k) : Short j (extVisibilityReplace x k i) := by
  rcases hx with rfl | rfl | ⟨u, rfl, hu⟩
  · exact Or.inl (extVisibilityReplace_bot _ _)
  · exact Or.inr (Or.inl (extVisibilityReplace_top _ _))
  · by_cases hut : finitePart u < k
    · rw [extVisibilityReplace_of_finitePart_lt hut]
      exact Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_limitPart_add_nat]; exact hi.trans hk⟩)
    · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp hut)]
      exact Or.inr (Or.inr ⟨u, rfl, hu⟩)

end
end VaughtConjecture.Knight.PrivateRowFactorization
