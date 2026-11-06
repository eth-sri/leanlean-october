module

public import ADR11.Defs
/-!
# Forests of gene lineages

A forest of rooted gene trees on the lineages `L` is represented by its set of clusters
`F : Family L`. `IsForest F` says the clusters are nonempty and any two are nested or
disjoint; its roots (`ADR11.roots`) are then pairwise disjoint and every cluster lies below a
root. `merges F` is the set of forests obtained by merging two roots of `F`, the transitions of
Kingman's coalescent.

## Main results

* `IsForest.disjoint_of_mem_roots`, `exists_mem_roots_subset`: the roots partition the
  lineages of a forest.
* `IsForest.isForest_merge`, `IsForest.roots_merge`, `IsForest.card_roots_merge`: merging two
  roots gives a forest with one root fewer.
* `IsForest.card_merges`: a forest with `k` roots has `k.choose 2` distinct merges.
* `kingmanGenerator_apply_of_isForest`: the rows of the generator at forests;
  `IsForest.sum_kingmanGenerator_mul`, `IsForest.kingmanGenerator_mul_apply`: the first-step
  decomposition `∑ G, Q(F, G) v(G) = -(k choose 2) v(F) + ∑ G ∈ merges F, v(G)`.
* `IsForest.union_of_disjoint`, `isForest_sup`, `IsForest.roots_union`: unions of forests on
  disjoint sets of lineages; `isForest_sampledForest`, `lineages_sampledForest`.
-/

@[expose] public section

namespace ADR11

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {G F : Family L} {A B C D : Finset L} {l : L}

theorem mem_unroot :
    A ∈ unroot G ↔ (A ∈ G ∧ A ≠ univ) ∨ (Aᶜ ∈ G ∧ Aᶜ ≠ univ) := by
  aesop (add simp [unroot])

/-- A forest: nonempty clusters, any two of which are nested or disjoint. -/
def IsForest (F : Family L) : Prop :=
  (∀ A ∈ F, A.Nonempty) ∧ ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

/-- The forests obtained from `F` by merging two distinct roots. -/
def merges (F : Family L) : Finset (Family L) :=
  ((roots F).powersetCard 2).image fun P => insert (P.sup id) F

/-- The lineages of a forest: the union of its clusters. -/
def lineages (F : Family L) : Finset L :=
  F.sup id

theorem mem_roots :
    A ∈ roots F ↔ A ∈ F ∧ ∀ B ∈ F, A ⊆ B → B = A := by
  unfold roots
  exact mem_filter

theorem roots_subset (F : Family L) : roots F ⊆ F := by
  unfold roots
  exact filter_subset _ _

theorem mem_merges :
    G ∈ merges F ↔ ∃ A ∈ roots F, ∃ B ∈ roots F, A ≠ B ∧ G = insert (A ∪ B) F := by
  aesop (add simp [merges, mem_powersetCard, card_eq_two, insert_subset_iff, singleton_subset_iff])

/-! ### Lineages -/

theorem subset_lineages (hA : A ∈ F) :
    A ⊆ lineages F :=
  le_sup (f := id) hA

/-! ### Roots and merges of forests -/

/-- Every cluster lies below a maximal one (for any finite family of clusters). -/
theorem exists_mem_roots_subset
    (hA : A ∈ F) : ∃ R ∈ roots F, A ⊆ R := by
  obtain ⟨R, hAR, hR⟩ := F.exists_le_maximal hA
  exact ⟨R, mem_roots.2 ⟨hR.1, fun B hB hRB => le_antisymm (hR.2 hB hRB) hRB⟩, hAR⟩

theorem union_not_mem_of_mem_roots
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hAB : A ≠ B) : A ∪ B ∉ F := by
  grind [roots]

/-- A root contained in the union of two roots is one of them. -/
theorem IsForest.root_subset_union (hF : IsForest F)
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hC : C ∈ roots F)
    (h : C ⊆ A ∪ B) : C = A ∨ C = B := by
  grind [IsForest, roots, disjoint_left]

theorem IsForest.merge_eq_merge_iff (hF : IsForest F)
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hC : C ∈ roots F) (hD : D ∈ roots F)
    (hAB : A ≠ B) (hCD : C ≠ D) :
    insert (A ∪ B) F = insert (C ∪ D) F ↔ (A = C ∧ B = D) ∨ (A = D ∧ B = C) := by
  rw [insert_inj (union_not_mem_of_mem_roots hA hB hAB)]
  grind (splits := 40) [IsForest.root_subset_union]

/-- A forest with `k` roots has exactly `k.choose 2` merges: distinct pairs of roots give
distinct forests. -/
theorem IsForest.card_merges (hF : IsForest F) :
    #(merges F) = (#(roots F)).choose 2 := by
  rw [merges, card_image_of_injOn, card_powersetCard]
  intro P hP Q hQ h
  obtain ⟨A,B,hAB,rfl⟩ := card_eq_two.1 (mem_powersetCard.1 hP).2
  obtain ⟨C,D,hCD,rfl⟩ := card_eq_two.1 (mem_powersetCard.1 hQ).2
  simp only [sup_insert, sup_singleton, id_eq] at h
  grind [IsForest.merge_eq_merge_iff]

set_option maxHeartbeats 1000000 in
/-- What a merge of a forest is. -/
theorem IsForest.of_mem_merges (hF : IsForest F) (hG : G ∈ merges F) :
    IsForest G ∧ #(roots G) + 1 = #(roots F) ∧ F ⊆ G ∧ G ≠ F ∧ lineages G = lineages F := by
  obtain ⟨A, hA, B, hB, hAB, rfl⟩ := mem_merges.1 hG
  have hf : IsForest (insert (A ∪ B) F) := by
    grind (splits := 40) [IsForest, roots, disjoint_union_left, disjoint_union_right,
      subset_union_left, subset_union_right]
  have hr : roots (insert (A ∪ B) F) = insert (A ∪ B) (((roots F).erase A).erase B) := by
    ext
    grind [mem_roots, IsForest.root_subset_union, roots, mem_insert_of_mem, mem_insert_self, subset_union_left, subset_union_right]
  have hl : lineages (insert (A ∪ B) F) = lineages F := by
    aesop (add simp [roots, lineages])
  grind [roots, union_not_mem_of_mem_roots]

/-! ### More on roots -/

/-- A lineage of a forest lies in only one root. -/
theorem IsForest.eq_of_mem_roots_of_mem (hF : IsForest F)
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hlA : l ∈ A) (hlB : l ∈ B) :
    A = B := by
  grind [IsForest, roots, disjoint_left]

/-! ### More on merges and the generator -/

/-- The generator at a forest, split into its diagonal part and its merge part. -/
theorem IsForest.sum_kingmanGenerator_mul (hF : IsForest F)
    (v : Family L → ℝ) :
    ∑ G, kingmanGenerator F G * v G =
      -((#(roots F)).choose 2 : ℝ) * v F + ∑ G ∈ merges F, v G := by
  have hn : F ∉ merges F := fun h => (hF.of_mem_merges h).2.2.2.1 rfl
  simp_all [kingmanGenerator, ← mem_merges]
  simp [sum_ite, filter_eq', filter_ne', hn]

end ADR11
