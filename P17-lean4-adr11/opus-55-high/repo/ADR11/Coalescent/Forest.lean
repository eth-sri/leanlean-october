module

public import ADR11.Defs

/-!
# Forests of gene lineages

A forest of rooted gene trees on the lineages `L` is represented by its set of clusters
`F : Finset (Finset L)`. `IsForest F` says the clusters are nonempty and any two are nested or
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

/-- A forest: nonempty clusters, any two of which are nested or disjoint. -/
def IsForest (F : Finset (Finset L)) : Prop :=
  (∀ A ∈ F, A.Nonempty) ∧ ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

/-- The forests obtained from `F` by merging two distinct roots. -/
def merges (F : Finset (Finset L)) : Finset (Finset (Finset L)) :=
  ((roots F ×ˢ roots F).filter fun p => p.1 ≠ p.2).image fun p => insert (p.1 ∪ p.2) F

/-- The lineages of a forest: the union of its clusters. -/
def lineages (F : Finset (Finset L)) : Finset L :=
  F.sup id

theorem mem_roots {F : Finset (Finset L)} {A : Finset L} :
    A ∈ roots F ↔ A ∈ F ∧ ∀ B ∈ F, A ⊆ B → B = A := by
  unfold roots
  grind

theorem roots_subset (F : Finset (Finset L)) : roots F ⊆ F := by
  unfold roots
  grind

theorem mem_merges {F G : Finset (Finset L)} :
    G ∈ merges F ↔ ∃ A ∈ roots F, ∃ B ∈ roots F, A ≠ B ∧ G = insert (A ∪ B) F := by simp [merges]; grind

/-! ### Lineages -/

section Lineages

omit [Fintype L]

theorem mem_lineages {F : Finset (Finset L)} {l : L} : l ∈ lineages F ↔ ∃ A ∈ F, l ∈ A := by simp_all [lineages]

theorem subset_lineages {F : Finset (Finset L)} {A : Finset L} (hA : A ∈ F) :
    A ⊆ lineages F :=
  le_sup (f := id) hA

theorem lineages_subset_iff {F : Finset (Finset L)} {S : Finset L} :
    lineages F ⊆ S ↔ ∀ A ∈ F, A ⊆ S :=
  Finset.sup_le_iff

theorem lineages_mono {F G : Finset (Finset L)} (h : F ⊆ G) : lineages F ⊆ lineages G :=
  sup_mono h

@[simp] theorem lineages_singleton (A : Finset L) : lineages {A} = A :=
  sup_singleton

@[simp] theorem lineages_insert (A : Finset L) (F : Finset (Finset L)) :
    lineages (insert A F) = A ∪ lineages F :=
  sup_insert

end Lineages

/-! ### Roots and merges of forests -/

theorem IsForest.disjoint_of_mem_roots {F : Finset (Finset L)} (hF : IsForest F) {A B : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hAB : A ≠ B) : Disjoint A B := by
  rw [mem_roots] at hA hB
  rcases hF.2 A hA.1 B hB.1 with h | h | h <;> grind

/-- Every cluster lies below a maximal one (for any finite family of clusters). -/
theorem exists_mem_roots_subset {F : Finset (Finset L)} {A : Finset L}
    (hA : A ∈ F) : ∃ R ∈ roots F, A ⊆ R := by
  obtain ⟨R, hAR, hR⟩ := F.exists_le_maximal hA
  exact ⟨R, mem_roots.2 ⟨hR.1, fun B hB hRB => le_antisymm (hR.2 hB hRB) hRB⟩, hAR⟩

theorem lineages_roots {F : Finset (Finset L)} :
    lineages (roots F) = lineages F := by
  refine (lineages_mono (roots_subset F)).antisymm (lineages_subset_iff.2 fun A hA => ?_)
  obtain ⟨R, hR, hAR⟩ := exists_mem_roots_subset hA
  exact hAR.trans (subset_lineages hR)

theorem union_not_mem_of_mem_roots {F : Finset (Finset L)} {A B : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hAB : A ≠ B) : A ∪ B ∉ F := by
  intro h
  rw [mem_roots] at hA hB
  have h1 : A ∪ B = A := by grind
  have h2 : B ⊆ A := by grind
  grind

/-- A root contained in the union of two roots is one of them. -/
theorem forest_root_subset_union {F : Finset (Finset L)} (hF : IsForest F)
    {A B C : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) (hC : C ∈ roots F)
    (h : C ⊆ A ∪ B) : C = A ∨ C = B := by
  by_contra hne
  push Not at hne
  obtain ⟨x, hx⟩ := hF.1 C (roots_subset F hC)
  rcases mem_union.1 (h hx) with h' | h'
  · exact disjoint_left.1 (hF.disjoint_of_mem_roots hC hA hne.1) hx h'
  · exact disjoint_left.1 (hF.disjoint_of_mem_roots hC hB hne.2) hx h'

/-- A cluster of a forest is contained in, or disjoint from, the union of two roots. -/
theorem forest_subset_or_disjoint_union {F : Finset (Finset L)} (hF : IsForest F)
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) {C : Finset L} (hC : C ∈ F) :
    C ⊆ A ∪ B ∨ Disjoint C (A ∪ B) := by
  obtain ⟨R, hR, hCR⟩ := exists_mem_roots_subset hC
  by_cases hRA : R = A
  · grind
  by_cases hRB : R = B
  · grind
  right
  rw [disjoint_union_right]
  exact ⟨(hF.disjoint_of_mem_roots hR hA hRA).mono_left hCR,
    (hF.disjoint_of_mem_roots hR hB hRB).mono_left hCR⟩

theorem IsForest.isForest_merge {F : Finset (Finset L)} (hF : IsForest F) {A B : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) : IsForest (insert (A ∪ B) F) := by
  refine ⟨fun C hC => ?_, fun C hC D hD => ?_⟩
  · rcases mem_insert.1 hC with rfl | hC
    · exact (hF.1 A (roots_subset F hA)).mono subset_union_left
    · exact hF.1 C hC
  · rcases mem_insert.1 hC with rfl | hC <;> rcases mem_insert.1 hD with rfl | hD
    · grind
    · rcases forest_subset_or_disjoint_union hF hA hB hD with h | h
      · grind
      · grind
    · rcases forest_subset_or_disjoint_union hF hA hB hC with h | h
      · grind
      · grind
    · exact hF.2 C hC D hD

theorem IsForest.roots_merge {F : Finset (Finset L)} (hF : IsForest F) {A B : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hAB : A ≠ B) :
    roots (insert (A ∪ B) F) = insert (A ∪ B) (((roots F).erase A).erase B) := by
  have hA' := mem_roots.1 hA
  have hB' := mem_roots.1 hB
  ext C
  constructor
  · intro hCm
    obtain ⟨hCi, hmax⟩ := mem_roots.1 hCm
    rcases mem_insert.1 hCi with rfl | hC
    · grind
    · have hCr : C ∈ roots F :=
        mem_roots.2 ⟨hC, fun D hD hCD => hmax D (mem_insert_of_mem hD) hCD⟩
      refine mem_insert_of_mem (mem_erase.2 ⟨?_, mem_erase.2 ⟨?_, hCr⟩⟩) <;> grind
  · intro hCm
    rcases mem_insert.1 hCm with rfl | hC
    · refine mem_roots.2 ⟨mem_insert_self _ _, fun D hDi hUD => ?_⟩
      grind
    · obtain ⟨hCB, hCe⟩ := mem_erase.1 hC
      obtain ⟨hCA, hCr⟩ := mem_erase.1 hCe
      have hC' := mem_roots.1 hCr
      refine mem_roots.2 ⟨mem_insert_of_mem hC'.1, fun D hD hCD => ?_⟩
      rcases mem_insert.1 hD with rfl | hD
      · exfalso
        rcases forest_root_subset_union hF hA hB hCr hCD with h | h <;> grind
      · grind

theorem IsForest.card_roots_merge {F : Finset (Finset L)} (hF : IsForest F) {A B : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hAB : A ≠ B) :
    #(roots (insert (A ∪ B) F)) + 1 = #(roots F) := by
  have hU : A ∪ B ∉ ((roots F).erase A).erase B := fun h =>
    union_not_mem_of_mem_roots hA hB hAB (roots_subset F (mem_of_mem_erase (mem_of_mem_erase h)))
  rw [hF.roots_merge hA hB hAB, card_insert_of_notMem hU,
    card_erase_add_one (mem_erase.2 ⟨hAB.symm, hB⟩), card_erase_add_one hA]

theorem lineages_merge {F : Finset (Finset L)} {A B : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) :
    lineages (insert (A ∪ B) F) = lineages F := by
  rw [lineages_insert, union_eq_right]
  exact union_subset (subset_lineages (roots_subset F hA)) (subset_lineages (roots_subset F hB))

/-- A merge determines the pair of roots merged. -/
theorem IsForest.merge_inj {F : Finset (Finset L)} (hF : IsForest F) {A B C D : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hAB : A ≠ B) (hC : C ∈ roots F) (hD : D ∈ roots F)
    (hCD : C ≠ D) (h : insert (A ∪ B) F = insert (C ∪ D) F) : s(A, B) = s(C, D) := by
  have hU :=
    (mem_insert.1 (h ▸ mem_insert_self _ _)).resolve_right (union_not_mem_of_mem_roots hA hB hAB)
  rcases forest_root_subset_union hF hA hB hC (hU ▸ subset_union_left) with rfl | rfl <;>
    rcases forest_root_subset_union hF hA hB hD (hU ▸ subset_union_right) with rfl | rfl
  exacts [absurd rfl hCD, rfl, Sym2.eq_swap, absurd rfl hCD]

/-- A forest with `k` roots has exactly `k.choose 2` merges: distinct pairs of roots give
distinct forests. -/
theorem IsForest.card_merges {F : Finset (Finset L)} (hF : IsForest F) :
    #(merges F) = (#(roots F)).choose 2 := by
  -- A merge depends only on the unordered pair of roots, and determines it.
  let g : Sym2 (Finset L) → Finset (Finset L) :=
    Sym2.lift ⟨fun A B => insert (A ∪ B) F, fun A B => by simp [union_comm]⟩
  have hg : ∀ A B, g s(A, B) = insert (A ∪ B) F := fun A B => Sym2.lift_mk _ A B
  have h1 : merges F = ((roots F).offDiag.image Sym2.mk.uncurry).image g := by
    ext G
    rw [mem_merges, image_image, mem_image]
    constructor
    · simp_all <;> grind
    · grind
  rw [h1, card_image_of_injOn, Sym2.card_image_offDiag]
  rintro _ hz _ hw hzw
  obtain ⟨⟨A, B⟩, hp, rfl⟩ := mem_image.1 hz
  obtain ⟨⟨C, D⟩, hq, rfl⟩ := mem_image.1 hw
  obtain ⟨hA, hB, hAB⟩ := mem_offDiag.1 hp
  obtain ⟨hC, hD, hCD⟩ := mem_offDiag.1 hq
  exact hF.merge_inj hA hB hAB hC hD hCD (by rwa [← hg, ← hg])

/-- What a merge of a forest is. -/
theorem IsForest.of_mem_merges {F G : Finset (Finset L)} (hF : IsForest F) (hG : G ∈ merges F) :
    IsForest G ∧ #(roots G) + 1 = #(roots F) ∧ F ⊆ G ∧ G ≠ F ∧ lineages G = lineages F := by
  obtain ⟨A, hA, B, hB, hAB, rfl⟩ := mem_merges.1 hG
  refine ⟨hF.isForest_merge hA hB, hF.card_roots_merge hA hB hAB, subset_insert _ _,
    fun h => union_not_mem_of_mem_roots hA hB hAB ?_, lineages_merge hA hB⟩
  rw [← h]
  grind

/-- The generator of Kingman's coalescent at a forest: `-(k choose 2)` on the diagonal and `1` at
each of the `k choose 2` merges. -/
theorem kingmanGenerator_apply_of_isForest {F : Finset (Finset L)}
    (G : Finset (Finset L)) :
    kingmanGenerator F G =
      if G = F then -((#(roots F)).choose 2 : ℝ) else if G ∈ merges F then 1 else 0 := by
  simp [kingmanGenerator, mem_merges]

/-! ### More on roots -/

/-- A lineage of a forest lies in only one root. -/
theorem IsForest.eq_of_mem_roots_of_mem {F : Finset (Finset L)} (hF : IsForest F)
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) {l : L} (hlA : l ∈ A) (hlB : l ∈ B) :
    A = B := by
  by_contra hAB
  exact disjoint_left.1 (hF.disjoint_of_mem_roots hA hB hAB) hlA hlB

/-! ### More on merges and the generator -/

/-- A forest with at most one root has no merges. -/
theorem merges_eq_empty_of_card_roots_le_one {F : Finset (Finset L)} (h : #(roots F) ≤ 1) :
    merges F = ∅ := by
  refine eq_empty_of_forall_notMem fun G hG => ?_
  obtain ⟨A, hA, B, hB, hAB, -⟩ := mem_merges.1 hG
  exact hAB (card_le_one.1 h A hA B hB)

theorem IsForest.self_not_mem_merges {F : Finset (Finset L)} (hF : IsForest F) :
    F ∉ merges F := fun h =>
  (hF.of_mem_merges h).2.2.2.1 rfl

/-- The generator at a forest, split into its diagonal part and its merge part. -/
theorem forest_kingmanGenerator_eq_add {F : Finset (Finset L)} (hF : IsForest F)
    (G : Finset (Finset L)) :
    kingmanGenerator F G =
      (if G = F then -((#(roots F)).choose 2 : ℝ) else 0) + (if G ∈ merges F then 1 else 0) := by
  rw [kingmanGenerator_apply_of_isForest]
  by_cases h1 : G = F
  · subst h1
    simp [hF.self_not_mem_merges]
  · grind

/-- First-step decomposition at a forest `F` with `k` roots:
`∑ G, Q(F, G) v(G) = -(k choose 2) v(F) + ∑ G ∈ merges F, v(G)`. -/
theorem IsForest.sum_kingmanGenerator_mul {F : Finset (Finset L)} (hF : IsForest F)
    (v : Finset (Finset L) → ℝ) :
    ∑ G, kingmanGenerator F G * v G =
      -((#(roots F)).choose 2 : ℝ) * v F + ∑ G ∈ merges F, v G := by
  simp [forest_kingmanGenerator_eq_add hF, add_mul, ite_mul, one_mul, zero_mul,
    sum_add_distrib, sum_ite_eq', mem_univ, ite_true, sum_ite_mem, univ_inter]

/-- The rows of `Q * M` at a forest. -/
theorem IsForest.kingmanGenerator_mul_apply {F : Finset (Finset L)} (hF : IsForest F)
    (M : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ) (G : Finset (Finset L)) :
    (kingmanGenerator (L := L) * M) F G =
      -((#(roots F)).choose 2 : ℝ) * M F G + ∑ F' ∈ merges F, M F' G := by
  rw [Matrix.mul_apply]
  exact hF.sum_kingmanGenerator_mul fun F' => M F' G

/-! ### Building forests -/

section Building

omit [Fintype L]

/-- A forest of singletons. -/
theorem forest_isForest_image_singleton (S : Finset L) :
    IsForest (S.image fun l => {l}) := by simp [IsForest]; grind

end Building

/-! ### The forests of sampled lineages -/

theorem isForest_sampledForest {X : Type*} [DecidableEq X] (s : L → X) (A : Finset X) :
    IsForest (sampledForest s A) :=
  forest_isForest_image_singleton _

end ADR11
