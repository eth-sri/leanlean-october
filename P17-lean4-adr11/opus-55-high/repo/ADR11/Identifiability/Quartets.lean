module

public import ADR11.External.Quartets.Steel

/-!
# Corollary 6's argument: quartet trees and their internal lengths determine `σ⁻`

The proof of Corollary 6 (l.574): "That all induced quartet topologies determine the topology
`ψ⁻` is well known [Steel 1992]. Because each internal edge of `ψ⁻` is the internal edge for some
induced quartet tree, `λ⁻` is determined as well."

* `SpeciesTree.sameUnrootedMetricTree_of_restrict`: two species trees whose induced unrooted
  metric trees agree on every set of four taxa have the same unrooted metric tree. The splits of
  `σ⁻` are compared through their quartets by Steel's reconstruction (`mem_unroot_iff_quartets`,
  with `SpeciesTree.restrict_unroot`), and the length of a split through a quartet that
  distinguishes it (`exists_distinguishing_quartet`, Steel's Proposition 6), whose induced split
  is induced by no other split (`SpeciesTree.restrict_unrootedLength`).

The same argument serves for nonbinary trees in Proposition 11, where the reconstruction is that of
Bandelt–Dress and Semple–Steel (Theorem 6.3.5), which `mem_unroot_iff_quartets` also covers.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- If `σ` and `σ'` induce the same unrooted trees on all sets of four taxa, every split of `σ⁻`
is a split of `σ'⁻`. -/
theorem quart_unroot_subset (σ σ' : SpeciesTree X)
    (h : ∀ Q : Finset X, ∀ hQ : Q.Nonempty, #Q = 4 →
      unroot (σ.restrict Q hQ).clusters = unroot (σ'.restrict Q hQ).clusters) :
    unroot σ.clusters ⊆ unroot σ'.clusters := by
  intro A hA
  obtain ⟨hAne, hAu⟩ := nonempty_of_mem_unroot σ.isHierarchy hA
  obtain ⟨hAcne, hAcu⟩ := nonempty_of_mem_unroot σ.isHierarchy (compl_mem_unroot.2 hA)
  by_cases h1 : #A ≤ 1
  · obtain ⟨x, rfl⟩ := card_eq_one.1 (le_antisymm h1 (card_pos.2 hAne))
    exact mem_unroot.2 (.inl ⟨σ'.singleton_mem x, hAu⟩)
  by_cases h2 : #Aᶜ ≤ 1
  · obtain ⟨x, hx⟩ := card_eq_one.1 (le_antisymm h2 (card_pos.2 hAcne))
    exact mem_unroot.2 (.inr ⟨hx ▸ σ'.singleton_mem x, hAcu⟩)
  rw [mem_unroot_iff_quartets σ' (by omega) (by omega)]
  intro a ha a' ha' b hb b' hb' haa hbb
  rw [mem_compl] at hb hb'
  have hQ : ({a, a', b, b'} : Finset X).Nonempty := by simp
  -- the trace of `A` on the quartet is a split of the quartet tree of `σ'`
  have h1 : A.subtype (· ∈ ({a, a', b, b'} : Finset X)) ∈ restrictSplits _ (unroot σ'.clusters) := by
    rw [← SpeciesTree.restrict_unroot σ' _ hQ, ← h _ hQ (by grind), SpeciesTree.restrict_unroot]
    exact mem_restrictSplits.2 ⟨A, hA, ⟨a, by simp [ha]⟩, ⟨b, by simp [hb]⟩, rfl⟩
  obtain ⟨C, hC, -, -, hCA⟩ := mem_restrictSplits.1 h1
  have key : ∀ x ∈ ({a, a', b, b'} : Finset X), x ∈ C ↔ x ∈ A := fun x => mem_iff_of_subtype_eq hCA
  grind

/-- Unrooted metric trees are determined by their quartets. -/
theorem SpeciesTree.sameUnrootedMetricTree_of_restrict (σ σ' : SpeciesTree X)
    (h : ∀ Q : Finset X, ∀ hQ : Q.Nonempty, #Q = 4 →
      (σ.restrict Q hQ).SameUnrootedMetricTree (σ'.restrict Q hQ)) :
    σ.SameUnrootedMetricTree σ' := by
  have hU :=
    Subset.antisymm (quart_unroot_subset σ σ' fun Q hQ hQ4 => (h Q hQ hQ4).1)
      (quart_unroot_subset σ' σ fun Q hQ hQ4 => (h Q hQ hQ4).1.symm)
  refine ⟨hU, fun A hA hA₁ hA₂ => ?_⟩
  obtain ⟨a, ha, a', ha', b, hb, b', hb', haa, hbb, hQ4, huniq⟩ :=
    exists_distinguishing_quartet σ hA hA₁ hA₂
  have hQ : ({a, a', b, b'} : Finset X).Nonempty := by simp
  -- the length of the split induced by `A` in an induced quartet tree is the length of `A`
  have hlen : ∀ τ : SpeciesTree X, unroot τ.clusters = unroot σ.clusters →
      (τ.restrict _ hQ).unrootedLength (A.subtype (· ∈ ({a, a', b, b'} : Finset X))) = τ.unrootedLength A := by
    intro τ hτ
    rw [restrict_unrootedLength τ hQ ⟨⟨a, by simp⟩, by simp [ha]⟩
      (subtype_ne_univ_iff.2 ⟨b, by simp [hb]⟩), unrootedLength]
    refine sum_congr (filter_congr fun B hB => and_congr_right fun hBu => ?_) fun _ _ => rfl
    have hBu := hτ ▸ mem_unroot.2 (.inl ⟨hB, hBu⟩)
    refine ⟨fun h => h.imp (fun h => huniq B hBu fun x => mem_iff_of_subtype_eq h) fun h => ?_,
      by rintro (rfl | rfl) <;> simp [subtype_compl]⟩
    rw [← huniq Bᶜ (compl_mem_unroot.2 hBu) fun x => mem_iff_of_subtype_eq
      (by rw [subtype_compl, h, compl_compl]), compl_compl]
  rw [← hlen σ rfl, ← hlen σ' hU.symm]
  refine (h _ hQ hQ4).2 _ ?_ (one_lt_card.2 ⟨⟨a, by simp⟩, by simp [ha], ⟨a', by simp⟩,
    by simp [ha'], by simp [haa]⟩) (one_lt_card.2 ⟨⟨b, by simp⟩, by simp [hb], ⟨b', by simp⟩,
    by simp [hb'], by simp [hbb]⟩)
  rw [SpeciesTree.restrict_unroot]
  exact mem_restrictSplits.2 ⟨A, hA, ⟨a, by simp [ha]⟩, ⟨b, by simp [hb]⟩, rfl⟩

end ADR11
