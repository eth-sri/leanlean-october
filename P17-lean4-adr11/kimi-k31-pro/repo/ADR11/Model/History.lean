module

public import ADR11.MSC.Basic

/-!
# Coalescent histories: the structure of gene tree probabilities (Section 3)

Helpers for `ADR11.Model`.

* `model_jumpMatrixQ`, `model_jumpMatrix_pow_apply`, `model_kingmanAbsorption_eq_rat`: the jump
  chain, hence the population above the root, has rational transition probabilities.
* `model_IsHistorySum D φ`: the function `φ` of the edge lengths is a sum, over finitely many
  coalescent histories `h`, of `c(h) ∏_{b ∈ D} g_{i(h,b) j(h,b)}(len b)`, with rational
  `c(h) > 0` and `1 ≤ j(h,b) ≤ i(h,b) ≤ #b`. Such sums are closed under sums, nonnegative rational
  multiples, and products of sums over disjoint sets of clusters.
* `model_forestDist_isHistorySum`: the history decomposition of the multispecies coalescent with
  one lineage per taxon, by induction over the clusters (the populations whose lengths appear are
  the clusters other than the root with at least two taxa, `model_internal`).
* `model_equation3`: equation (3); `model_section3_polynomial`: gene tree probabilities are
  polynomials with rational coefficients in the `exp (-x_b)`.
* `model_forestDist_congr_internal`: with one lineage per taxon, pendant edge lengths do not
  matter.
* `model_rootedDist_support`: with at least one lineage, gene trees are binary hierarchies with
  probability `1`.
-/

@[expose] public section

namespace ADR11

open Finset Real

/-! ### The jump chain has rational transition probabilities -/

section Rational

variable {L : Type*} [Fintype L] [DecidableEq L]

end Rational

/-! ### Sums over coalescent histories -/

section HistorySum

variable {X : Type*}

/-- `φ`, a function of the edge lengths, is a sum over finitely many coalescent histories `h` of
`c(h) ∏_{b ∈ D} g_{i(h,b) j(h,b)}(len b)`, with rational `c(h) > 0` and
`1 ≤ j(h,b) ≤ i(h,b) ≤ #b`. -/
def model_IsHistorySum (D : Finset (Finset X)) (φ : (Finset X → ℝ) → ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℚ) (i j : ι → Finset X → ℕ),
    (∀ h, 0 < c h) ∧ (∀ h, ∀ b ∈ D, 1 ≤ j h b ∧ j h b ≤ i h b ∧ i h b ≤ #b) ∧
    ∀ len, φ len = ∑ h : ι, (c h : ℝ) * ∏ b ∈ D, deathProb (i h b) (j h b) (len b)

theorem model_IsHistorySum.congr {D : Finset (Finset X)} {φ ψ : (Finset X → ℝ) → ℝ}
    (h : model_IsHistorySum D φ) (e : ∀ len, ψ len = φ len) : model_IsHistorySum D ψ := by
  obtain ⟨ι, _, c, i, j, hc, hij, hφ⟩ := h
  exact ⟨ι, inferInstance, c, i, j, hc, hij, fun len => (e len).trans (hφ len)⟩

end HistorySum

/-! ### The history decomposition -/

section Decomposition

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Polynomials in the transformed branch lengths -/

/-! ### Pendant edges -/

end Decomposition

/-! ### Gene trees are binary -/

section Binary

variable {X : Type*} [Fintype X] [DecidableEq X] {L : Type*} [Fintype L] [DecidableEq L]

/-- Every cluster with at least two elements is the union of two disjoint clusters. -/
def model_IsBinaryForest (F : Finset (Finset L)) : Prop :=
  ∀ A ∈ F, 2 ≤ #A → ∃ B ∈ F, ∃ C ∈ F, Disjoint B C ∧ B ∪ C = A

theorem model_isBinaryForest_merge {F G : Finset (Finset L)} (hF : IsForest F)
    (hb : model_IsBinaryForest F) (hG : G ∈ merges F) : model_IsBinaryForest G := by
  obtain ⟨A, hA, B, hB, hAB, rfl⟩ := mem_merges.1 hG
  intro C hC hC2
  rcases mem_insert.1 hC with rfl | hC
  · exact ⟨A, mem_insert_of_mem (roots_subset F hA), B, mem_insert_of_mem (roots_subset F hB),
      hF.disjoint_of_mem_roots hA hB hAB, rfl⟩
  · obtain ⟨D, hD, E, hE, hDE, hDEC⟩ := hb C hC hC2
    exact ⟨D, mem_insert_of_mem hD, E, mem_insert_of_mem hE, hDE, hDEC⟩

theorem model_isBinaryForest_of_jumpMatrix_pow {F G : Finset (Finset L)} (hF : IsForest F)
    (hb : model_IsBinaryForest F) {n : ℕ} (h : (jumpMatrix ^ n) F G ≠ 0) :
    model_IsBinaryForest G := by
  induction n generalizing F with
  | zero =>
    rw [pow_zero] at h
    by_cases hGF : G = F
    · exact hGF ▸ hb
    · exact absurd (Matrix.one_apply_ne (Ne.symm hGF)) h
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply] at h
    obtain ⟨F', -, hF'⟩ := exists_ne_zero_of_sum_ne_zero h
    have hJ := left_ne_zero_of_mul hF'
    have hJn := right_ne_zero_of_mul hF'
    by_cases hk : #(roots F) ≤ 1
    · have hF'F : F' = F := by
        by_contra hne
        exact hJ (by simp only [jumpMatrix, hk, hne, ↓reduceIte])
      subst hF'F
      exact ih hF hb hJn
    · have hmem : F' ∈ merges F := by
        by_contra hne
        exact hJ (by rw [jumpMatrix_apply_of_isForest (by omega), ite_eq_right hne])
      exact ih (hF.of_mem_merges hmem).1 (model_isBinaryForest_merge hF hb hmem) hJn

theorem model_isBinaryForest_of_populationKernel {len : Finset X → ℝ} {A : Finset X}
    {F G : Finset (Finset L)} (hF : IsForest F) (hb : model_IsBinaryForest F)
    (h : populationKernel len A F G ≠ 0) : model_IsBinaryForest G := by
  unfold populationKernel at h
  split_ifs at h with hA
  · rw [kingmanAbsorption_apply hF] at h
    split_ifs at h with h0 h1 h2
    · exact h1 ▸ hb
    · exact absurd rfl h
    · exact model_isBinaryForest_of_jumpMatrix_pow hF hb h
    · exact absurd rfl h
  · rw [kingmanTransition_apply hF] at h
    exact model_isBinaryForest_of_jumpMatrix_pow hF hb (right_ne_zero_of_mul h)

theorem model_isBinaryForest_of_forestDist {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) (s : L → X) {A : Finset X} (hA : A ∈ H) {G : Finset (Finset L)}
    (hG : forestDist H len s A G ≠ 0) : model_IsBinaryForest G := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist] at hG
  obtain ⟨f, -, hf⟩ := exists_ne_zero_of_sum_ne_zero hG
  have hprod := left_ne_zero_of_mul hf
  have hfB : ∀ B : childClusters H A,
      IsForest (f B) ∧ lineages (f B) = univ.filter (fun l => s l ∈ (B : Finset X)) := by
    intro B
    obtain ⟨h1, -, h3⟩ := forestDist_support hH len s (mem_childClusters.1 B.2).1
      (prod_ne_zero_iff.1 hprod B (mem_univ _))
    exact ⟨h1, h3⟩
  have hbB : ∀ B : childClusters H A, model_IsBinaryForest (f B) := fun B =>
    ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1
      (prod_ne_zero_iff.1 hprod B (mem_univ _))
  refine model_isBinaryForest_of_populationKernel (hH.isForest_entering f hfB).1 ?_
    (right_ne_zero_of_mul hf)
  intro C hC hC2
  rcases mem_union.1 hC with hC | hC
  · obtain ⟨B, -, hCB⟩ := mem_sup.1 hC
    obtain ⟨D, hD, E, hE, hDE, hDEC⟩ := hbB B C hCB hC2
    exact ⟨D, mem_union_left _ (mem_sup.2 ⟨B, mem_univ _, hD⟩),
      E, mem_union_left _ (mem_sup.2 ⟨B, mem_univ _, hE⟩), hDE, hDEC⟩
  · obtain ⟨l, -, rfl⟩ := mem_sampledForest.1 hC
    simp at hC2

/-- Sections 1 and 5: with at least one lineage, a rooted gene tree with positive probability is a
binary hierarchy on the lineages. (With no lineage at all, the only gene tree is the empty forest,
which is not a hierarchy.) -/
theorem model_rootedDist_support [Nonempty L] (σ : SpeciesTree X) (s : L → X)
    {G : Finset (Finset L)} (hG : σ.rootedDist s G ≠ 0) :
    IsHierarchy G ∧ ∀ A ∈ G, 2 ≤ #A → ∃ B ∈ G, ∃ C ∈ G, Disjoint B C ∧ B ∪ C = A := by
  obtain ⟨h1, h2, h3, -⟩ := forestDist_univ_support σ.isHierarchy σ.length s hG
  have hsing : ∀ l : L, {l} ∈ G := fun l => h2 (singleton_mem_sampledForest.2 (mem_univ _))
  have hk : #(roots G) = 1 := by
    have := (roots_nonempty_iff.2 ⟨_, hsing (Classical.arbitrary L)⟩).card_pos
    have h4 := (forestDist_univ_support σ.isHierarchy σ.length s hG).2.2.2
    omega
  have huniv : (univ : Finset L) ∈ G := h3 ▸ lineages_mem_of_card_roots_eq_one hk
  exact ⟨⟨huniv, hsing, h1.1, h1.2⟩,
    model_isBinaryForest_of_forestDist σ.isHierarchy σ.length s σ.univ_mem hG⟩

end Binary

end ADR11
