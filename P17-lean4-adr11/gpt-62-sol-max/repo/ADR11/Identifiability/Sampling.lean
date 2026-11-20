module

public import ADR11.MSC.MultiSample
public import ADR11.Nonbinary.Theorem9

@[expose] public section

namespace ADR11
open Finset
variable {X : Type*} [Fintype X] [DecidableEq X]

private theorem sample_bound (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x) (S : Finset X)
    (hS : ∀ x ∈ S, 2 ≤ ℓ x) : Fintype.card X + #S ≤ Fintype.card (Σ x, Fin (ℓ x)) := by
  have H x : 1 + (if x ∈ S then 1 else 0) ≤ ℓ x := by split_ifs <;> grind
  simpa [Fintype.card_sigma, sum_add_distrib] using sum_le_sum (s := univ) fun x _ => H x

/-- Apply rooted identifiability to the tree with one new leaf per sampled lineage. -/
theorem identifiability_of_samples
    (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hc : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X) = σ'.unrootedDist Sigma.fst) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} := by
  have ⟨hX, h5⟩ : 2 ≤ Fintype.card X ∧ 5 ≤ Fintype.card (Σ x, Fin (ℓ x)) := by
    rcases hc with ⟨h4, x, hx⟩ | ⟨h3, x, y, hxy, hx, hy⟩
    · have := sample_bound ℓ hℓ {x} (by simpa)
      grind
    · have := sample_bound ℓ hℓ {x, y} (by simpa using And.intro hx hy)
      grind [card_pair hxy]
  let s : (Σ x, Fin (ℓ x)) → X := Sigma.fst
  have hs : Function.Surjective s := fun x => ⟨⟨x, ⟨0, hℓ x⟩⟩, rfl⟩
  have he := rooted_identifiability h5 (σ.extend s hs) (σ'.extend s hs)
    (by simpa only [SpeciesTree.unrootedDist_extend] using h)
  obtain ⟨hr, hp⟩ := SpeciesTree.sameRootedMetricTree_of_extend hX σ σ' hs he
  refine ⟨hr, fun x hx => hp x ?_⟩
  dsimp [s]
  rw [← Finset.univ_sigma_univ, Finset.filter_sigma, Finset.card_sigma]
  simpa [filter_const, apply_ite, sum_ite_eq'] using hx

end ADR11
