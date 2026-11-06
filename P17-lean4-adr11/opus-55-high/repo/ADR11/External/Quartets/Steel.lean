module

public import ADR11.Trees.Hierarchy

/-!
# Unrooted trees are determined by their quartets

[M. Steel, *The complexity of reconstructing trees from qualitative characters and subtrees*,
J. Classification 9 (1992) 91–116], used in the proofs of Corollary 6 (binary trees) and of
Theorem 9 (Proposition 6 there: every internal edge is distinguished by a quartet); for trees
that need not be binary, [H.-J. Bandelt, A. Dress, *Reconstructing the shape of a tree from
observed dissimilarity data*, Adv. Appl. Math. 7 (1986) 309–343] and [C. Semple, M. Steel,
*Phylogenetics*, Oxford University Press, 2003, Theorem 6.3.5], used in the proof of
Proposition 11.

In the representation of `ADR11.unroot`, these are statements about the sets of splits of the
unrooted trees `σ⁻` of species trees:

* `mem_unroot_iff_quartets`: a bipartition `A | Aᶜ` with `|A|, |Aᶜ| ≥ 2` is a split of `σ⁻` if and
  only if every quartet `aa'|bb'` with `a, a' ∈ A` and `b, b' ∈ Aᶜ` is displayed by `σ⁻`.
* `exists_distinguishing_quartet`: every internal edge of `σ⁻` is the only edge of `σ⁻` separating
  some quartet `aa'|bb'` (Steel's Proposition 6, for trees that need not be binary).

Corollary 6 combines them with its own argument for the edge lengths
(`ADR11.Identifiability.Quartets`).

## Proofs

* `mem_unroot_iff_quartets`: rerooting `σ⁻` at a taxon `b₀ ∉ A`, the sides of the splits of `σ⁻`
  not containing `b₀`, together with `univ` and `{b₀}`, form a hierarchy, in which `A` is a
  cluster by the rooted-triple criterion `IsHierarchy.mem_of_triples`.
* `exists_distinguishing_quartet`: for a cluster `A` of `σ`, take `a, a'` in different children
  of `A`, `b ∈ P \ A` for the parent `P` of `A`, and `b' ∉ A` such that no cluster strictly
  contained in `Aᶜ` contains both `b` and `b'`.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A split `A | Aᶜ` (with both sides of size at least 2) is a split of `σ⁻` if and only if every
quartet `aa'|bb'` (`a ≠ a'` in `A`, `b ≠ b'` in `Aᶜ`) is displayed by `σ⁻`, that is, separated by
some split of `σ⁻`. -/
theorem mem_unroot_iff_quartets (σ : SpeciesTree X) {A : Finset X} (hA : 2 ≤ #A)
    (hA' : 2 ≤ #Aᶜ) :
    A ∈ unroot σ.clusters ↔
      ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ Aᶜ, ∀ b' ∈ Aᶜ, a ≠ a' → b ≠ b' →
        ∃ C ∈ unroot σ.clusters, a ∈ C ∧ a' ∈ C ∧ b ∉ C ∧ b' ∉ C := by
  refine ⟨fun h a ha a' ha' b hb b' hb' _ _ => ⟨A, h, ha, ha', mem_compl.1 hb, mem_compl.1 hb'⟩,
    fun hq => ?_⟩
  obtain ⟨b₀, hb₀⟩ : Aᶜ.Nonempty := card_pos.1 (by omega)
  obtain ⟨b₁, hb₁, hb₁₀⟩ := exists_mem_ne (show 1 < #Aᶜ by omega) b₀
  -- the clusters of `σ⁻` rerooted at the leaf `b₀`
  have hH : IsHierarchy (insert univ (insert {b₀} ((unroot σ.clusters).filter (b₀ ∉ ·)))) := by
    refine ⟨mem_insert_self _ _, fun x => ?_, ?_, ?_⟩ <;> simp only [mem_insert, mem_filter]
    · by_cases hx : x = b₀ <;> by_cases hu : ({x} : Finset X) = univ <;>
        simp_all [mem_unroot, σ.singleton_mem, eq_comm]
    · rintro C (rfl | rfl | ⟨h, -⟩)
      exacts [⟨b₀, mem_univ _⟩, singleton_nonempty _, (nonempty_of_mem_unroot σ.isHierarchy h).1]
    · rintro C (rfl | rfl | ⟨hC, hC₀⟩) D (rfl | rfl | ⟨hD, hD₀⟩) <;> try simp [*]
      rcases unroot_compat σ hC hD with h | h | h | h <;> grind [mem_compl]
  have key := hH.mem_of_triples (A := A) (card_pos.1 (by omega)) fun a ha a' ha' b hb => by
    by_cases haa : a = a'
    · exact ⟨{a}, by simp [hH.2.1], by simp, by simp [← haa], by grind⟩
    by_cases hbb : b = b₀
    · simp_all <;> grind
    · simp_all <;> grind
  simp at key
  rcases key with rfl | rfl | h
  exacts [absurd (mem_univ b₀) (mem_compl.1 hb₀), absurd (mem_singleton_self b₀) (mem_compl.1 hb₀), h.1]

/-- For `x ∈ N ≠ {x}`, a taxon `y ∈ N` such that no cluster strictly contained in `N` contains
both `x` and `y`: any taxon outside the child of `N` containing `x`. -/
theorem steel_exists_pair (σ : SpeciesTree X) {N : Finset X} {x : X} (hx : x ∈ N)
    (hN : 2 ≤ #N) : ∃ y ∈ N, x ≠ y ∧ ∀ C ∈ σ.clusters, x ∈ C → y ∈ C → ¬ C ⊂ N := by
  obtain ⟨B, hB, hxB⟩ := σ.isHierarchy.exists_mem_childClusters_of_ne hx (by rintro rfl; simp at hN)
  obtain ⟨y, hyN, hyB⟩ := exists_of_ssubset (mem_childClusters.1 hB).2.1
  exact ⟨y, hyN, fun h => hyB (h ▸ hxB), fun C hC hxC hyC hCN => hyB
    (σ.isHierarchy.subset_of_mem_childClusters hB hC hCN (not_disjoint_iff.2 ⟨x, hxB, hxC⟩) hyC)⟩

/-- Steel's Proposition 6: every internal edge `A | Aᶜ` of `σ⁻` is the only split of `σ⁻`
separating some quartet `aa'|bb'`. -/
theorem exists_distinguishing_quartet (σ : SpeciesTree X) {A : Finset X}
    (hA : A ∈ unroot σ.clusters) (hA₁ : 2 ≤ #A) (hA₂ : 2 ≤ #Aᶜ) :
    ∃ a ∈ A, ∃ a' ∈ A, ∃ b ∉ A, ∃ b' ∉ A, a ≠ a' ∧ b ≠ b' ∧ #({a, a', b, b'} : Finset X) = 4 ∧
      ∀ C ∈ unroot σ.clusters, (∀ x ∈ ({a, a', b, b'} : Finset X), x ∈ C ↔ x ∈ A) → C = A := by
  wlog hA1 : A ∈ σ.clusters generalizing A
  · obtain ⟨a, ha, a', ha', b, hb, b', hb', haa, hbb, -, h⟩ := this (compl_mem_unroot.2 hA) hA₂
      (by rwa [compl_compl]) ((mem_unroot.1 hA).resolve_left (by tauto)).1
    simp only [mem_compl, not_not] at *
    exact ⟨b, hb, b', hb', a, ha, a', ha', hbb, haa, by grind, fun C hC hx => compl_injective
      (h _ (compl_mem_unroot.2 hC) (by simp; grind))⟩
  obtain ⟨a, ha⟩ : A.Nonempty := card_pos.1 (by omega)
  obtain ⟨a', ha', haa, hpair⟩ := steel_exists_pair σ ha hA₁
  -- the parent `P` of `A`
  obtain ⟨P, hP, hPmin⟩ := exists_min_image (σ.clusters.filter fun C => A ⊂ C) card
    ⟨univ, mem_filter.2 ⟨σ.univ_mem, ssubset_univ_iff.2 ((nonempty_of_mem_unroot σ.isHierarchy hA).2)⟩⟩
  obtain ⟨hPc, hAP⟩ := mem_filter.1 hP
  obtain ⟨b, hbP, hbA⟩ := exists_of_ssubset hAP
  obtain ⟨b', hb', hbb, hpair'⟩ := steel_exists_pair σ (mem_compl.2 hbA) hA₂
  refine ⟨a, ha, a', ha', b, hbA, b', mem_compl.1 hb', haa, hbb,
    by clear * - ha ha' haa hbA hb' hbb; grind [mem_compl], fun C hC hx => ?_⟩
  have haC := (hx a (by simp)).2 ha
  have ha'C := (hx a' (by simp)).2 ha'
  have hbC := fun h => hbA ((hx b (by simp)).1 h)
  have hb'C := fun h => mem_compl.1 hb' ((hx b' (by simp)).1 h)
  rcases mem_unroot.1 hC with ⟨hC1, -⟩ | ⟨hC1, -⟩ <;> by_contra hne
  · rcases σ.laminar C hC1 A hA1 with h | h | h
    · simp_all <;> grind
    · have hle := hPmin C (mem_filter.2 ⟨hC1, ssubset_of_subset_of_ne h (Ne.symm hne)⟩)
      rcases σ.laminar C hC1 P hPc with h' | h' | h'
      · exact hbC (eq_of_subset_of_card_le h' hle ▸ hbP)
      · simp_all <;> grind
      · simp_all <;> grind
    · exact disjoint_left.1 h haC ha
  · rcases σ.laminar Cᶜ hC1 A hA1 with h | h | h
    · exact mem_compl.1 hb' (h (mem_compl.2 hb'C))
    · exact mem_compl.1 (h ha) haC
    · exact hpair' Cᶜ hC1 (mem_compl.2 hbC) (mem_compl.2 hb'C) (ssubset_of_subset_of_ne
        (subset_compl_iff_disjoint_right.2 h) fun h' => hne (compl_injective h'))

end ADR11
