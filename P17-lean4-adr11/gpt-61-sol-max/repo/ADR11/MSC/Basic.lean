module

public import ADR11.Coalescent.Absorption
/-!
# Basic properties of the multispecies coalescent

The recursion `ADR11.forestDist` is defined for any family of clusters `H` and any lengths; most
results here assume `H` is a hierarchy (`IsHierarchy H`) and the lengths are nonnegative.

* `enteringDist H len s A`: the distribution of the forest entering the population above `A`.
* `unrootedDistOf H len s`: the distribution of unrooted gene trees, for raw data; it is
  `SpeciesTree.unrootedDist` for a species tree.

## Main results

* `forestDist_eq_sum_entering`: `forestDist` is the entering distribution pushed through the
  population kernel.
* `forestDist_of_childClusters_eq_empty`, `forestDist_of_childClusters_eq_pair`,
  `forestDist_of_childClusters_eq_triple`: unfolding at a leaf, at a node with two children and
  at a node with three children (and the same for `enteringDist`).
* `forestDist_singleton_of_card_le_one`, `forestDist_id_singleton`: at a leaf from which at most
  one lineage is sampled, the leaving forest is the sampled forest.
* `IsHierarchy.disjoint_of_mem_childClusters`, `IsHierarchy.sup_childClusters`,
  `IsHierarchy.two_le_card_childClusters`: the children of a cluster with at least two elements
  partition it; `IsHierarchy.childClusters_eq`, `IsHierarchy.childClusters_eq_pair`,
  `IsHierarchy.childClusters_eq_triple`: recognizing the children;
  `SpeciesTree.isBinary_iff_card_childClusters`: a species tree is binary if and only if every
  such cluster has exactly two children.
* `forestDist_support`: the forest leaving the population above `A` is a forest on exactly the
  lineages sampled from `A`, containing their singletons (`enteringDist_support`: the same for the
  entering forest; `forestDist_univ_support`: above the root, it has at most one root).
* `forestDist_nonneg`, `forestDist_nonneg_of_ne_univ`, `forestDist_sum`, `forestDist_le_one`,
  `enteringDist_nonneg_of_ne_univ`, `enteringDist_sum`,
  `unrootedDistOf_nonneg`, `unrootedDistOf_sum`: probability distributions.
* `forestDist_congr_len`: only the lengths of the edges below the root matter.
* `unrootedDistOf_eq_sum_entering`: the unrooted distribution is obtained from the forest entering
  the population above the root through `unrootedOutcome`.
-/

@[expose] public section

namespace ADR11

open Finset
open scoped Matrix

variable {X : Type*} [Fintype X] [DecidableEq X] {L : Type*} [Fintype L] [DecidableEq L]
variable {H K : Family X} {s : L → X} {A B C : Finset X} {F G : Family L} {x : X}

/-- A hierarchy of clusters on `X`. -/
def IsHierarchy (H : Family X) : Prop :=
  univ ∈ H ∧ (∀ x : X, {x} ∈ H) ∧ (∀ A ∈ H, A.Nonempty) ∧
    ∀ A ∈ H, ∀ B ∈ H, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

theorem SpeciesTree.isHierarchy (σ : SpeciesTree X) : IsHierarchy σ.clusters :=
  ⟨σ.univ_mem, σ.singleton_mem, σ.nonempty_of_mem, σ.laminar⟩

/-- The distribution of the forest entering the population above `A`: the union of the
independent forests leaving the populations of the children of `A`, together with the singletons
of the lineages sampled at `A`. -/
noncomputable def enteringDist (H : Family X) (len : Finset X → ℝ) (s : L → X)
    (A : Finset X) (F : Family L) : ℝ :=
  ∑ f : childClusters H A → Family L,
    if univ.sup f ∪ sampledForest s A = F then ∏ B : childClusters H A, forestDist H len s B (f B)
    else 0

theorem forestDist_eq_sum_entering (H : Family X) (len : Finset X → ℝ) (s : L → X)
    (A : Finset X) :
    forestDist H len s A = enteringDist H len s A ᵥ* populationKernel len A := by
  funext G
  unfold Matrix.vecMul dotProduct
  rw [forestDist]
  unfold enteringDist
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

theorem forestDist_of_childClusters_eq_empty {len : Finset X → ℝ}
    (h : childClusters H A = ∅) (G : Family L) :
    forestDist H len s A G = populationKernel len A (sampledForest s A) G := by
  rw [forestDist]
  have : IsEmpty (childClusters H A) := by rw [h]; infer_instance
  rw [Fintype.sum_unique]
  simp

theorem mem_childClusters :
    B ∈ childClusters H A ↔ B ∈ H ∧ B ⊂ A ∧ ∀ C ∈ H, B ⊂ C → ¬ C ⊂ A :=
  mem_filter

theorem childClusters_image (f : Finset X ↪o Finset L) (H : Family X) (A : Finset X) :
    childClusters (H.image f) (f A) = (childClusters H A).image f := by
  simp [childClusters, filter_image]
theorem childClusters_union_eq
    (h : ∀ B ∈ K, B ⊂ A → ∃ C ∈ H, B ⊆ C ∧ C ⊂ A) :
    childClusters (H ∪ K) A = childClusters H A := by
  ext B
  simp_all [childClusters]
  grind

/-- In a hierarchy, the children of a cluster with at least two elements partition it, and a
singleton has no children. -/
theorem IsHierarchy.childClusters_singleton (hH : IsHierarchy H) (x : X) :
    childClusters H {x} = ∅ := by
  aesop (add simp [childClusters, IsHierarchy])

/-- Two distinct children of a cluster of a hierarchy are disjoint. -/
theorem IsHierarchy.disjoint_of_mem_childClusters (hH : IsHierarchy H)
    (hB : B ∈ childClusters H A) (hC : C ∈ childClusters H A) (hBC : B ≠ C) :
    Disjoint B C := by
  grind [IsHierarchy, childClusters]

theorem mem_sampledForest {C : Finset L} :
    C ∈ sampledForest s A ↔ ∃ l, s l ∈ A ∧ {l} = C := by
  simp [sampledForest]

/-- The forest entering the population above a cluster `A` of a hierarchy, when the forests
leaving the children are forests on the lineages sampled from the children, is a forest on the
lineages sampled from `A`, containing their singletons. -/
theorem IsHierarchy.isForest_entering (hH : IsHierarchy H)
    (f : childClusters H A → Family L)
    (hf : ∀ B, IsForest (f B) ∧ lineages (f B) = clusterPreimage s B) :
    IsForest (univ.sup f ∪ sampledForest s A) ∧
      sampledForest s A ⊆ univ.sup f ∪ sampledForest s A ∧
      lineages (univ.sup f ∪ sampledForest s A) = clusterPreimage s A := by
  have hsub (B : childClusters H A) {C} (hC : C ∈ f B) :=
    (hf B).2 ▸ subset_lineages hC
  have hd (B C : Finset X) (hB : B ∈ childClusters H A) (hC : C ∈ childClusters H A) :
      B = C ∨ Disjoint B C := by
    grind [IsHierarchy.disjoint_of_mem_childClusters]
  refine ⟨?_, subset_union_right, ?_⟩
  · grind [IsForest, mem_childClusters, mem_sup, mem_sampledForest,
      singleton_nonempty, mem_singleton_self, disjoint_left]
  · ext l
    simp only [lineages, mem_sup, id_eq]
    grind [mem_sup, mem_sampledForest, mem_singleton_self,
      mem_childClusters]

section
variable (hH : IsHierarchy H) (len : Finset X → ℝ) (s : L → X)
include hH

/-- The forest leaving the population above a cluster `A` of a hierarchy is a forest on exactly
the lineages sampled from `A`, containing the singletons of all of them. -/
theorem forestDist_support  (hG : forestDist H len s A G ≠ 0) :
    IsForest G ∧ sampledForest s A ⊆ G ∧ lineages G = clusterPreimage s A := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist] at hG
  obtain ⟨f, -, hf⟩ := Finset.exists_ne_zero_of_sum_ne_zero hG
  obtain ⟨hF, hSF, hLF⟩ := hH.isForest_entering f (by
    intro B
    exact (ih B (mem_childClusters.1 B.2).2.1 (Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hf) B (mem_univ _))).imp_right And.right
  )
  have hK := right_ne_zero_of_mul hf
  unfold populationKernel at hK
  split_ifs at hK <;>
    simp only [kingmanAbsorption_eq_jump hF, kingmanTransition_apply hF] at hK <;>
    obtain ⟨hGf, hFG, hlin, -⟩ := jumpMatrix_pow_support hF
      (by first | exact hK | exact right_ne_zero_of_mul hK) <;>
    exact ⟨hGf, hSF.trans hFG, hlin.trans hLF⟩

/-- Nonzero choices of the child forests give a valid entering forest. -/
private theorem entering_support_of_prod

    {f : childClusters H A → Family L}
    (hf : (∏ B : childClusters H A, forestDist H len s B (f B)) ≠ 0) :
    IsForest (univ.sup f ∪ sampledForest s A) ∧
      sampledForest s A ⊆ univ.sup f ∪ sampledForest s A ∧
      lineages (univ.sup f ∪ sampledForest s A) = clusterPreimage s A := by
  apply hH.isForest_entering f
  intro B
  exact (forestDist_support hH len s
    (prod_ne_zero_iff.1 hf B (mem_univ _))).imp_right And.right

/-- Nonnegativity, assuming only that the lengths of the edges below the root are nonnegative
(the length at `univ` is irrelevant). -/
theorem forestDist_nonneg_of_ne_univ
    {len : Finset X → ℝ} (hlen : ∀ A ∈ H, A ≠ univ → 0 ≤ len A) (s : L → X)
    (hA : A ∈ H) (G : Family L) : 0 ≤ forestDist H len s A G := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist]
  refine Finset.sum_nonneg fun f _ => ?_
  by_cases hprod : ∏ B : childClusters H A, forestDist H len s B (f B) = 0
  · rw [hprod, zero_mul]
  · refine mul_nonneg (Finset.prod_nonneg fun B _ => ?_) ?_
    · exact ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1 _
    · have hF := (entering_support_of_prod hH len s hprod).1
      unfold populationKernel
      split_ifs with hAu
      · rw [kingmanAbsorption_eq_jump hF]
        exact Matrix.pow_apply_nonneg (by intros; unfold jumpMatrix; split_ifs <;> positivity) _ _ _
      · exact kingmanTransition_nonneg (hlen A hA hAu) _ G

theorem forestDist_sum : ∑ G, forestDist H len s A G = 1 := by
  induction A using Finset.strongInduction with
  | H A ih =>
  conv_lhs => arg 2; intro G; rw [forestDist]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  trans ∑ f : childClusters H A → Family L, ∏ B : childClusters H A, forestDist H len s B (f B)
  · apply sum_congr rfl
    intro f _
    by_cases hprod : ∏ B : childClusters H A, forestDist H len s B (f B) = 0
    · rw [hprod, zero_mul]
    · have hF := (entering_support_of_prod hH len s hprod).1
      unfold populationKernel
      split_ifs
      · have h := tendsto_finsetSum univ fun G _ => tendsto_kingmanTransition hF G
        simp only [kingmanTransition_sum hF] at h
        rw [tendsto_nhds_unique h tendsto_const_nhds, mul_one]
      · rw [kingmanTransition_sum hF, mul_one]
  · rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one fun B _ => ih B (mem_childClusters.1 B.2).2.1

/-! ### The entering distribution -/

/-- The forest entering the population above a cluster `A` of a hierarchy is a forest on exactly
the lineages sampled from `A`, containing the singletons of all of them. -/
theorem enteringDist_support  (hF : enteringDist H len s A F ≠ 0) :
    IsForest F ∧ sampledForest s A ⊆ F ∧ lineages F = clusterPreimage s A := by
  unfold enteringDist at hF
  obtain ⟨f, -, hf⟩ := Finset.exists_ne_zero_of_sum_ne_zero hF
  split_ifs at hf with hfF
  · subst hfF
    exact entering_support_of_prod hH len s hf
  · exact absurd rfl hf

end

/-! ### The children of a cluster of a hierarchy -/

theorem IsHierarchy.exists_mem_childClusters_superset (hB : B ∈ H) (hBA : B ⊂ A) :
    ∃ C ∈ childClusters H A, B ⊆ C := by
  obtain ⟨C, hBC, hC⟩ := (H.filter (· ⊂ A)).exists_le_maximal (mem_filter.2 ⟨hB, hBA⟩)
  refine ⟨C, mem_childClusters.2 ⟨(mem_filter.1 hC.1).1, (mem_filter.1 hC.1).2, ?_⟩, hBC⟩
  intro D hD hCD hDA
  exact not_subset_of_ssubset hCD (hC.2 (mem_filter.2 ⟨hD, hDA⟩) hCD.subset)

section
variable (hH : IsHierarchy H) (len : Finset X → ℝ)
include hH

/-- Every element of a cluster `A` with at least two elements lies in a child of `A`. -/
theorem IsHierarchy.exists_mem_childClusters
    (hA : 2 ≤ #A) (hx : x ∈ A) : ∃ B ∈ childClusters H A, x ∈ B := by
  obtain ⟨B, hB, hxB⟩ := IsHierarchy.exists_mem_childClusters_superset (hH.2.1 x)
    (show {x} ⊂ A by grind)
  exact ⟨B, hB, hxB (mem_singleton_self x)⟩

/-! ### Leaves -/

/-- At a leaf `{x}` from which at most one lineage is sampled, the forest leaving the population
is the sampled forest, whatever the length of the pendant edge. -/
theorem forestDist_id_singleton (x : X) (G : Family X) :
    forestDist H len id {x} G = if G = sampledForest id {x} then 1 else 0 := by
  rw [forestDist_of_childClusters_eq_empty (hH.childClusters_singleton x)]
  have hF : IsForest (sampledForest id {x}) := by
    grind [IsForest, sampledForest, singleton_nonempty, disjoint_singleton_left]
  have hk : #(roots (sampledForest id {x})) ≤ 1 := by
    simpa [sampledForest, Finset.filter_eq'] using
      (card_le_card (roots_subset (sampledForest id ({x} : Finset X))))
  unfold populationKernel
  split
  · rw [kingmanAbsorption_eq_jump hF, jumpMatrix_pow_of_card_roots_le_one hk]
  · exact kingmanTransition_of_card_roots_le_one hF hk _ G

/-! ### Dependence on the lengths -/

/-! ### Species trees: probability distributions -/

end

end ADR11
