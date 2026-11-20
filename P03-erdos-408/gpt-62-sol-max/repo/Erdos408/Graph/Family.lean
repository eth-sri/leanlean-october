module

public import Erdos408.Graph.Reindex

/-!
# The family conclusion of `GraphTransference`

`FamilyBound` is the conclusion of `GraphTransference` for given groups at
scale `x`: a family of comparison patterns with the transferred pairing
bound. It transports along a reindexing of the groups (`FamilyBound.reindex`),
so it suffices to construct it for groups indexed by `Fin n`.
-/

@[expose] public section

namespace Erdos408.Graph

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
/-- The slot product of transported slots and labels. -/
lemma slotProduct_reindex (e : ι ≃ κ) {J : ℕ} (A : κ → Finset (Fin J)) (a : ι → Fin J → ℕ) :
    slotProduct (fun g => A (e g)) a = slotProduct A fun k => a (e.symm k) := by
  unfold slotProduct
  rw [← Equiv.prod_comp e]
  simp only [Equiv.symm_apply_apply]

/-- `FamilyBound` for the reindexed groups gives it for the original ones. -/
lemma FamilyBound.reindex (e : ι ≃ κ) {q₀ : ℝ} {m₀ J : ℕ} {C₁ C E C₃ C₄ x : ℝ}
    {P : ι → Finset ℕ} {big : Finset ι}
    (h : FamilyBound q₀ m₀ J C₁ C E C₃ C₄ x (fun k => P (e.symm k)) (big.map e.toEmbedding)) :
    FamilyBound q₀ m₀ J C₁ C E C₃ C₄ x P big := by
  obtain ⟨N, A, B, β, φ, φ', ψ, ψ', U, U', hpat, hmass, hpair⟩ := h
  refine ⟨N, fun ν g => A ν (e g), fun ν g => B ν (e g), β, φ, φ', ψ, ψ', U, U', ?_, hmass, ?_⟩
  · intro ν
    obtain ⟨h₁, h₂, ⟨⟨g, hg⟩, ⟨g', hg'⟩⟩, h₄, h₅, h₆⟩ := hpat ν
    exact ⟨fun g => h₁ (e g), fun g hg => h₂ (e g) (by simpa using hg),
      ⟨⟨e.symm g, by simpa using hg⟩, ⟨e.symm g', by simpa using hg'⟩⟩, h₄, h₅, h₆⟩
  intro ζ hζ X hX₁ hX₂ S S' f g hS hf hg hnf hng
  have := hpair ζ hζ X hX₁ hX₂ S S' f g hS hf hg (by rwa [physicalNormSq_reindex])
    (by rwa [physicalNormSq_reindex])
  have hraw := patternPairing_reindex e P q₀ (fun _ => (∅ : Finset (Fin J)))
    (fun _ _ _ => 1) ζ S f g
  rw [← hraw]
  convert this using 4 with ν
  rw [← patternPairing_reindex e]
  simp only [Equiv.apply_symm_apply, slotProduct_reindex]

end Erdos408.Graph
