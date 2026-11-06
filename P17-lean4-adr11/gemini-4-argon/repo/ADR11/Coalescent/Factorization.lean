module

public import ADR11.Defs

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X] {L : Type*} [Fintype L] [DecidableEq L]

def restrictClusters (S : Finset X) (H : Finset (Finset X)) : Finset (Finset S) :=
  (H.filter fun A => (A ∩ S).Nonempty).image fun A => A.subtype (· ∈ S)

def hierarchyOf (C : Finset (Finset X)) : Finset (Finset X) :=
  insert univ (C ∪ univ.image fun x => {x})

def treeOfClusters (C : Finset (Finset X)) : Finset (Finset X) :=
  unroot (hierarchyOf C)

def T5 : ℕ → Finset (Finset (Fin 5))
  | 1 => treeOfClusters {{0, 1}, {0, 1, 2}}
  | 4 => treeOfClusters {{0, 2}, {0, 1, 2}}
  | 5 => treeOfClusters {{0, 2}, {0, 2, 3}}
  | 6 => treeOfClusters {{0, 2}, {0, 2, 4}}
  | 7 => treeOfClusters {{0, 3}, {0, 1, 3}}
  | _ => ∅

noncomputable def u (σ : SpeciesTree (Fin 5)) (i : ℕ) : ℝ :=
  σ.unrootedDist id (T5 i)

namespace SpeciesTree

noncomputable def restrictLength (σ : SpeciesTree X) (S : Finset X) (C : Finset S) : ℝ :=
  ∑ A ∈ σ.clusters with A ≠ univ ∧ A.subtype (· ∈ S) = C, σ.length A

noncomputable def restrict (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    SpeciesTree S where
  clusters := restrictClusters S σ.clusters
  univ_mem := mem_image.2 ⟨univ, mem_filter.2 ⟨σ.univ_mem, by simpa using hS⟩, by simp⟩
  singleton_mem x := mem_image.2 ⟨{x.1}, mem_filter.2 ⟨σ.singleton_mem x.1, ⟨x.1, by simp [x.2]⟩⟩,
    by ext ⟨y, hy⟩; simp [Subtype.ext_iff]⟩
  nonempty_of_mem C hC := by
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hC
    obtain ⟨y, hy⟩ := (mem_filter.1 hA).2
    rw [mem_inter] at hy
    exact ⟨⟨y, hy.2⟩, by simp [hy.1]⟩
  laminar C hC D hD := by
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hC
    obtain ⟨B, hB, rfl⟩ := mem_image.1 hD
    rcases σ.laminar A (mem_filter.1 hA).1 B (mem_filter.1 hB).1 with h | h | h
    · exact Or.inl (subtype_mono h)
    · exact Or.inr (Or.inl (subtype_mono h))
    · exact Or.inr (Or.inr (disjoint_left.2 fun a ha hb =>
        disjoint_left.1 h (mem_subtype.1 ha) (mem_subtype.1 hb)))
  length := σ.restrictLength S
  length_pos C hC hCu := by
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hC
    exact Finset.sum_pos (fun B hB => σ.length_pos B (mem_filter.1 hB).1 (mem_filter.1 hB).2.1)
      ⟨A, mem_filter.2 ⟨(mem_filter.1 hA).1, fun e => hCu (e ▸ subtype_univ _), rfl⟩⟩

end SpeciesTree

def IsForest (F : Finset (Finset L)) : Prop :=
  (∀ A ∈ F, A.Nonempty) ∧ ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

def merges (F : Finset (Finset L)) : Finset (Finset (Finset L)) :=
  ((roots F ×ˢ roots F).filter fun p => p.1 ≠ p.2).image fun p => insert (p.1 ∪ p.2) F

def lineages (F : Finset (Finset L)) : Finset L := F.sup id

theorem mem_roots {F : Finset (Finset L)} {A : Finset L} :
    A ∈ roots F ↔ A ∈ F ∧ ∀ B ∈ F, A ⊆ B → B = A := mem_filter

theorem roots_subset (F : Finset (Finset L)) : roots F ⊆ F := filter_subset _ _

theorem mem_merges {F G : Finset (Finset L)} :
    G ∈ merges F ↔ ∃ A ∈ roots F, ∃ B ∈ roots F, A ≠ B ∧ G = insert (A ∪ B) F := by
  unfold merges
  simp only [mem_image, mem_filter, mem_product, Prod.exists]
  exact ⟨fun ⟨A, B, ⟨⟨hA, hB⟩, hAB⟩, h⟩ => ⟨A, hA, B, hB, hAB, h.symm⟩,
    fun ⟨A, hA, B, hB, hAB, h⟩ => ⟨A, B, ⟨⟨hA, hB⟩, hAB⟩, h.symm⟩⟩

section Lineages

omit [Fintype L]

theorem mem_lineages {F : Finset (Finset L)} {l : L} : l ∈ lineages F ↔ ∃ A ∈ F, l ∈ A := by
  unfold lineages; simp only [mem_sup, id]

theorem subset_lineages {F : Finset (Finset L)} {A : Finset L} (hA : A ∈ F) :
    A ⊆ lineages F := le_sup (f := id) hA

@[simp] theorem lineages_insert (A : Finset L) (F : Finset (Finset L)) :
    lineages (insert A F) = A ∪ lineages F := sup_insert

end Lineages

theorem IsForest.disjoint_of_mem_roots {F : Finset (Finset L)} (hF : IsForest F) {A B : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hAB : A ≠ B) : Disjoint A B := by
  rw [mem_roots] at hA hB
  rcases hF.2 A hA.1 B hB.1 with h | h | h
  · exact absurd (hA.2 B hB.1 h).symm hAB
  · exact absurd (hB.2 A hA.1 h) hAB
  · exact h

theorem exists_mem_roots_subset {F : Finset (Finset L)} {A : Finset L}
    (hA : A ∈ F) : ∃ R ∈ roots F, A ⊆ R := by
  obtain ⟨R, hAR, hR⟩ := F.exists_le_maximal hA
  exact ⟨R, mem_roots.2 ⟨hR.1, fun B hB hRB => le_antisymm (hR.2 hB hRB) hRB⟩, hAR⟩

theorem lineages_roots {F : Finset (Finset L)} :
    lineages (roots F) = lineages F := by
  refine (sup_mono (roots_subset F)).antisymm (Finset.sup_le fun A hA => ?_)
  obtain ⟨R, hR, hAR⟩ := exists_mem_roots_subset hA
  exact hAR.trans (subset_lineages hR)

theorem union_not_mem_of_mem_roots {F : Finset (Finset L)} {A B : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hAB : A ≠ B) : A ∪ B ∉ F := fun h => by
  rw [mem_roots] at hA hB
  exact hAB (hB.2 A hA.1 (hA.2 _ h subset_union_left ▸ subset_union_right))

private theorem forest_root_subset_union {F : Finset (Finset L)} (hF : IsForest F)
    {A B C : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) (hC : C ∈ roots F)
    (h : C ⊆ A ∪ B) : C = A ∨ C = B := by
  by_contra hne
  push Not at hne
  obtain ⟨x, hx⟩ := hF.1 C (roots_subset F hC)
  rcases mem_union.1 (h hx) with h' | h'
  · exact disjoint_left.1 (hF.disjoint_of_mem_roots hC hA hne.1) hx h'
  · exact disjoint_left.1 (hF.disjoint_of_mem_roots hC hB hne.2) hx h'

private theorem forest_subset_or_disjoint_union {F : Finset (Finset L)} (hF : IsForest F)
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) {C : Finset L} (hC : C ∈ F) :
    C ⊆ A ∪ B ∨ Disjoint C (A ∪ B) := by
  obtain ⟨R, hR, hCR⟩ := exists_mem_roots_subset hC
  by_cases hRA : R = A
  · exact Or.inl (hCR.trans (hRA ▸ subset_union_left))
  by_cases hRB : R = B
  · exact Or.inl (hCR.trans (hRB ▸ subset_union_right))
  exact Or.inr (disjoint_union_right.2 ⟨(hF.disjoint_of_mem_roots hR hA hRA).mono_left hCR,
    (hF.disjoint_of_mem_roots hR hB hRB).mono_left hCR⟩)

theorem IsForest.isForest_merge {F : Finset (Finset L)} (hF : IsForest F) {A B : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) : IsForest (insert (A ∪ B) F) := by
  refine ⟨fun C hC => ?_, fun C hC D hD => ?_⟩
  · rcases mem_insert.1 hC with rfl | hC
    · exact (hF.1 A (roots_subset F hA)).mono subset_union_left
    · exact hF.1 C hC
  · rcases mem_insert.1 hC with rfl | hC <;> rcases mem_insert.1 hD with rfl | hD
    · exact Or.inl subset_rfl
    · exact Or.inr ((forest_subset_or_disjoint_union hF hA hB hD).imp id fun h => h.symm)
    · exact (forest_subset_or_disjoint_union hF hA hB hC).imp id Or.inr
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
    · exact mem_insert_self _ _
    · refine mem_insert_of_mem (mem_erase.2 ⟨?_, mem_erase.2 ⟨?_,
        mem_roots.2 ⟨hC, fun D hD hCD => hmax D (mem_insert_of_mem hD) hCD⟩⟩⟩)
      · rintro rfl
        exact hAB (hA'.2 C hC (hmax _ (mem_insert_self _ _) subset_union_right ▸ subset_union_left)).symm
      · rintro rfl
        exact hAB (hB'.2 C hC (hmax _ (mem_insert_self _ _) subset_union_left ▸ subset_union_right))
  · intro hCm
    rcases mem_insert.1 hCm with rfl | hC
    · refine mem_roots.2 ⟨mem_insert_self _ _, fun D hDi hUD => ?_⟩
      rcases mem_insert.1 hDi with rfl | hD
      · rfl
      · have h1 : D = A := hA'.2 D hD (subset_union_left.trans hUD)
        subst h1
        exact absurd (hB'.2 D hD (subset_union_right.trans hUD)) hAB
    · obtain ⟨hCB, hCe⟩ := mem_erase.1 hC
      obtain ⟨hCA, hCr⟩ := mem_erase.1 hCe
      have hC' := mem_roots.1 hCr
      refine mem_roots.2 ⟨mem_insert_of_mem hC'.1, fun D hD hCD => ?_⟩
      rcases mem_insert.1 hD with rfl | hD
      · rcases forest_root_subset_union hF hA hB hCr hCD with h | h
        · exact absurd h hCA
        · exact absurd h hCB
      · exact hC'.2 D hD hCD

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

theorem IsForest.merge_eq_iff {F : Finset (Finset L)} (hF : IsForest F) {A B C D : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hAB : A ≠ B)
    (hC : C ∈ roots F) (hD : D ∈ roots F) (hCD : C ≠ D) :
    insert (A ∪ B) F = insert (C ∪ D) F ↔ (A = C ∧ B = D) ∨ (A = D ∧ B = C) := by
  refine ⟨fun hzw => ?_, ?_⟩
  · have hU : A ∪ B = C ∪ D := (mem_insert.1 (hzw ▸ mem_insert_self _ _)).resolve_right
      (union_not_mem_of_mem_roots hA hB hAB)
    rcases forest_root_subset_union hF hA hB hC (hU ▸ subset_union_left) with rfl | rfl <;>
      rcases forest_root_subset_union hF hA hB hD (hU ▸ subset_union_right) with rfl | rfl
    · exact absurd rfl hCD
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hCD
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · rw [union_comm]

theorem IsForest.card_merges {F : Finset (Finset L)} (hF : IsForest F) :
    #(merges F) = (#(roots F)).choose 2 := by
  let g : Sym2 (Finset L) → Finset (Finset L) :=
    Sym2.lift ⟨fun A B => insert (A ∪ B) F, fun A B => by simp only [union_comm]⟩
  have hg : ∀ A B, g s(A, B) = insert (A ∪ B) F := fun A B => Sym2.lift_mk _ A B
  have h1 : merges F = ((roots F).offDiag.image Sym2.mk.uncurry).image g := by
    ext G; rw [mem_merges, image_image, mem_image]
    constructor
    · rintro ⟨A, hA, B, hB, hAB, rfl⟩
      exact ⟨(A, B), mem_offDiag.2 ⟨hA, hB, hAB⟩, hg A B⟩
    · rintro ⟨⟨A, B⟩, hp, rfl⟩
      obtain ⟨hA, hB, hAB⟩ : A ∈ roots F ∧ B ∈ roots F ∧ A ≠ B := mem_offDiag.1 hp
      exact ⟨A, hA, B, hB, hAB, (hg A B).symm⟩
  rw [h1, card_image_of_injOn, Sym2.card_image_offDiag]
  rintro _ hz _ hw hzw
  obtain ⟨⟨A, B⟩, hp, rfl⟩ := mem_image.1 hz
  obtain ⟨⟨C, D⟩, hq, rfl⟩ := mem_image.1 hw
  obtain ⟨hA, hB, hAB⟩ := mem_offDiag.1 hp
  obtain ⟨hC, hD, hCD⟩ := mem_offDiag.1 hq
  exact Sym2.eq_iff.2 ((hF.merge_eq_iff hA hB hAB hC hD hCD).1 (by simpa [hg] using hzw))

theorem IsForest.of_mem_merges {F G : Finset (Finset L)} (hF : IsForest F) (hG : G ∈ merges F) :
    IsForest G ∧ #(roots G) + 1 = #(roots F) ∧ F ⊆ G ∧ G ≠ F ∧ lineages G = lineages F := by
  obtain ⟨A, hA, B, hB, hAB, rfl⟩ := mem_merges.1 hG
  exact ⟨hF.isForest_merge hA hB, hF.card_roots_merge hA hB hAB, subset_insert _ _,
    fun h => union_not_mem_of_mem_roots hA hB hAB (h ▸ mem_insert_self _ _), lineages_merge hA hB⟩

theorem kingmanGenerator_apply_of_isForest {F : Finset (Finset L)}
    (G : Finset (Finset L)) :
    kingmanGenerator F G =
      if G = F then -((#(roots F)).choose 2 : ℝ) else if G ∈ merges F then 1 else 0 := by
  simp only [kingmanGenerator, mem_merges]

theorem IsForest.eq_of_mem_roots_of_mem {F : Finset (Finset L)} (hF : IsForest F)
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) {l : L} (hlA : l ∈ A) (hlB : l ∈ B) :
    A = B :=
  by_contra fun hAB => disjoint_left.1 (hF.disjoint_of_mem_roots hA hB hAB) hlA hlB

theorem merges_eq_empty_of_card_roots_le_one {F : Finset (Finset L)} (h : #(roots F) ≤ 1) :
    merges F = ∅ := by
  refine eq_empty_of_forall_notMem fun G hG => ?_
  obtain ⟨A, hA, B, hB, hAB, -⟩ := mem_merges.1 hG
  exact hAB (card_le_one.1 h A hA B hB)

theorem IsForest.sum_kingmanGenerator_mul {F : Finset (Finset L)} (hF : IsForest F)
    (v : Finset (Finset L) → ℝ) :
    ∑ G, kingmanGenerator F G * v G =
      -((#(roots F)).choose 2 : ℝ) * v F + ∑ G ∈ merges F, v G := by
  have hadd : ∀ G, kingmanGenerator F G =
      (if G = F then -((#(roots F)).choose 2 : ℝ) else 0) + (if G ∈ merges F then 1 else 0) :=
    fun G => by
      rw [kingmanGenerator_apply_of_isForest]
      by_cases h1 : G = F
      · subst h1; simp [show G ∉ merges G from fun h => (hF.of_mem_merges h).2.2.2.1 rfl]
      · simp [h1]
  simp only [hadd, add_mul, ite_mul, one_mul, zero_mul,
    sum_add_distrib, sum_ite_eq', mem_univ, ite_true, sum_ite_mem, univ_inter]

theorem IsForest.kingmanGenerator_mul_apply {F : Finset (Finset L)} (hF : IsForest F)
    (M : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ) (G : Finset (Finset L)) :
    (kingmanGenerator (L := L) * M) F G =
      -((#(roots F)).choose 2 : ℝ) * M F G + ∑ F' ∈ merges F, M F' G := by
  rw [Matrix.mul_apply]
  exact hF.sum_kingmanGenerator_mul fun F' => M F' G

theorem isForest_sampledForest {X : Type*} [DecidableEq X] (s : L → X) (A : Finset X) :
    IsForest (sampledForest s A) := by
  refine ⟨fun B hB => ?_, fun B hB C hC => ?_⟩
  · obtain ⟨l, -, rfl⟩ := mem_image.1 hB; exact singleton_nonempty l
  · obtain ⟨l, -, rfl⟩ := mem_image.1 hB
    obtain ⟨m, -, rfl⟩ := mem_image.1 hC
    by_cases hlm : l = m
    · exact Or.inl (hlm ▸ subset_rfl)
    · exact Or.inr (Or.inr (disjoint_singleton.2 hlm))

noncomputable def jumpMatrix : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  fun F G =>
    if #(roots F) ≤ 1 then (if G = F then 1 else 0)
    else if G ∈ merges F then (((#(roots F)).choose 2 : ℕ) : ℝ)⁻¹ else 0

def deathPow : ℕ → ℕ → ℕ → ℝ
  | 0, k, j => if k = j then 1 else 0
  | m + 1, k, j => ((k.choose 2 : ℕ) : ℝ) * (deathPow m (k - 1) j - deathPow m k j)

noncomputable def deathProb (k j : ℕ) (t : ℝ) : ℝ :=
  ∑' m : ℕ, t ^ m / (m.factorial : ℝ) * deathPow m k j

theorem jumpMatrix_apply_of_isForest {F : Finset (Finset L)}
    (hk : 2 ≤ #(roots F)) (G : Finset (Finset L)) :
    jumpMatrix F G = if G ∈ merges F then (((#(roots F)).choose 2 : ℕ) : ℝ)⁻¹ else 0 := by
  simp only [jumpMatrix, ite_eq_right (by omega : ¬ #(roots F) ≤ 1)]

private theorem fact_jumpMatrix_apply_of_le_one {F : Finset (Finset L)} (hk : #(roots F) ≤ 1)
    (G : Finset (Finset L)) : jumpMatrix F G = if G = F then 1 else 0 := by
  simp only [jumpMatrix, ite_eq_left hk]

omit [Fintype L] in
private theorem fact_one_apply (F G : Finset (Finset L)) :
    (1 : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ) F G = if G = F then 1 else 0 := by
  by_cases h : G = F
  · subst h; simp
  · rw [Matrix.one_apply_ne (Ne.symm h), ite_eq_right h]

theorem jumpMatrix_pow_succ_apply {F : Finset (Finset L)} (hk : 2 ≤ #(roots F))
    (n : ℕ) (G : Finset (Finset L)) :
    (jumpMatrix ^ (n + 1)) F G =
      (((#(roots F)).choose 2 : ℕ) : ℝ)⁻¹ * ∑ F' ∈ merges F, (jumpMatrix ^ n) F' G := by
  rw [pow_succ', Matrix.mul_apply]
  simp_rw [jumpMatrix_apply_of_isForest hk, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]

theorem jumpMatrix_pow_of_card_roots_le_one {F : Finset (Finset L)} (hk : #(roots F) ≤ 1)
    (n : ℕ) (G : Finset (Finset L)) :
    (jumpMatrix ^ n) F G = if G = F then 1 else 0 := by
  induction n with
  | zero => rw [pow_zero, fact_one_apply]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [fact_jumpMatrix_apply_of_le_one hk, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ F), ih]

theorem jumpMatrix_pow_nonneg (n : ℕ) (F G : Finset (Finset L)) : 0 ≤ (jumpMatrix ^ n) F G := by
  induction n generalizing F with
  | zero => rw [pow_zero, fact_one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg fun F' _ =>
      mul_nonneg (by simp only [jumpMatrix]; split_ifs <;> positivity) (ih F')

theorem jumpMatrix_pow_support {F G : Finset (Finset L)} (hF : IsForest F) {n : ℕ}
    (h : (jumpMatrix ^ n) F G ≠ 0) :
    IsForest G ∧ F ⊆ G ∧ lineages G = lineages F ∧
      #(roots G) = if n < #(roots F) then #(roots F) - n else min (#(roots F)) 1 := by
  induction n generalizing F with
  | zero =>
    rw [pow_zero, fact_one_apply] at h
    split_ifs at h with hGF
    · subst hGF; refine ⟨hF, subset_rfl, rfl, ?_⟩; split_ifs <;> omega
    · exact absurd rfl h
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply] at h
    obtain ⟨F', -, hF'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hJ : jumpMatrix F F' ≠ 0 := left_ne_zero_of_mul hF'
    have hJn : (jumpMatrix ^ n) F' G ≠ 0 := right_ne_zero_of_mul hF'
    by_cases hk : #(roots F) ≤ 1
    · have hF'F : F' = F := by_contra fun hne =>
        hJ (by rw [fact_jumpMatrix_apply_of_le_one hk, ite_eq_right hne])
      subst hF'F
      obtain ⟨h1, h2, h3, h4⟩ := ih hF hJn
      refine ⟨h1, h2, h3, ?_⟩; rw [h4]; split_ifs <;> omega
    · replace hk : 2 ≤ #(roots F) := by omega
      have hmem : F' ∈ merges F := by_contra fun hne =>
        hJ (by rw [jumpMatrix_apply_of_isForest hk, ite_eq_right hne])
      obtain ⟨hF'f, hcard, hsub, -, hlin⟩ := hF.of_mem_merges hmem
      obtain ⟨h1, h2, h3, h4⟩ := ih hF'f hJn
      refine ⟨h1, hsub.trans h2, h3.trans hlin, ?_⟩; rw [h4]; split_ifs <;> omega

theorem deathPow_succ (m k j : ℕ) :
    deathPow (m + 1) k j = ((k.choose 2 : ℕ) : ℝ) * (deathPow m (k - 1) j - deathPow m k j) :=
  rfl

theorem deathPow_eq_zero_of_lt {k j : ℕ} (h : k < j) (m : ℕ) : deathPow m k j = 0 := by
  induction m generalizing k with
  | zero => simp [deathPow, h.ne]
  | succ m ih => rw [deathPow_succ, ih (lt_of_le_of_lt (Nat.sub_le k 1) h), ih h, sub_self, mul_zero]

theorem deathPow_self (m k : ℕ) : deathPow m k k = (-((k.choose 2 : ℕ) : ℝ)) ^ m := by
  induction m with
  | zero => simp [deathPow]
  | succ m ih =>
    rw [deathPow_succ, ih]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [deathPow_eq_zero_of_lt (Nat.sub_lt hk one_pos)]; ring

private theorem fact_abs_deathPow_le (m k j : ℕ) :
    |deathPow m k j| ≤ (2 * ((k.choose 2 : ℕ) : ℝ)) ^ m := by
  induction m generalizing k with
  | zero => simp only [deathPow, pow_zero]; split_ifs <;> simp
  | succ m ih =>
    rw [deathPow_succ, abs_mul, pow_succ, abs_of_nonneg (by positivity)]
    have hc : (((k - 1).choose 2 : ℕ) : ℝ) ≤ ((k.choose 2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_le_choose 2 (Nat.sub_le k 1)
    have h1 : |deathPow m (k - 1) j| ≤ (2 * ((k.choose 2 : ℕ) : ℝ)) ^ m :=
      (ih (k - 1)).trans (pow_le_pow_left₀ (by positivity) (by linarith) m)
    have h2 := ih k
    calc ((k.choose 2 : ℕ) : ℝ) * |deathPow m (k - 1) j - deathPow m k j|
        ≤ ((k.choose 2 : ℕ) : ℝ) * (|deathPow m (k - 1) j| + |deathPow m k j|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) (by positivity)
      _ ≤ ((k.choose 2 : ℕ) : ℝ) *
            ((2 * ((k.choose 2 : ℕ) : ℝ)) ^ m + (2 * ((k.choose 2 : ℕ) : ℝ)) ^ m) := by gcongr
      _ = (2 * ((k.choose 2 : ℕ) : ℝ)) ^ m * (2 * ((k.choose 2 : ℕ) : ℝ)) := by ring

theorem hasSum_deathProb (k j : ℕ) (t : ℝ) :
    HasSum (fun m : ℕ => t ^ m / (m.factorial : ℝ) * deathPow m k j) (deathProb k j t) := by
  refine (Summable.of_norm_bounded
    (Real.summable_pow_div_factorial (|t| * (2 * ((k.choose 2 : ℕ) : ℝ)))) fun m => ?_).hasSum
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast]
  calc |t| ^ m / (m.factorial : ℝ) * |deathPow m k j|
      ≤ |t| ^ m / (m.factorial : ℝ) * (2 * ((k.choose 2 : ℕ) : ℝ)) ^ m := by
        gcongr; exact fact_abs_deathPow_le m k j
    _ = (|t| * (2 * ((k.choose 2 : ℕ) : ℝ))) ^ m / (m.factorial : ℝ) := by ring

theorem fact_hasSum_exp_mul (x t : ℝ) :
    HasSum (fun m : ℕ => t ^ m / (m.factorial : ℝ) * x ^ m) (Real.exp (x * t)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (x * t)
  rw [← Real.exp_eq_exp_ℝ] at h
  convert h using 1; funext m; rw [mul_pow]; ring

theorem deathProb_self (k : ℕ) (t : ℝ) :
    deathProb k k t = exp (-(((k.choose 2 : ℕ) : ℝ) * t)) := by
  rw [← neg_mul]
  refine HasSum.tsum_eq ?_
  simp_rw [deathPow_self]
  exact fact_hasSum_exp_mul _ t

set_option backward.isDefEq.respectTransparency false in
theorem fact_hasSum_exp_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (i j : ι) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ))⁻¹ * (A ^ n) i j) (NormedSpace.exp A i j) := by
  open scoped Matrix.Norms.Operator in
  simpa using Pi.hasSum.mp (Pi.hasSum.mp (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A) i) j

theorem kingmanGenerator_pow_apply {F : Finset (Finset L)} (hF : IsForest F) (m : ℕ)
    (G : Finset (Finset L)) :
    (kingmanGenerator ^ m) F G =
      deathPow m (#(roots F)) (#(roots G)) * (jumpMatrix ^ (#(roots F) - #(roots G))) F G := by
  induction m generalizing F with
  | zero =>
    rw [pow_zero, fact_one_apply]
    simp only [deathPow]
    by_cases h : G = F
    · subst h; simp
    · rw [ite_eq_right h]
      split_ifs with hk
      · rw [hk, Nat.sub_self, pow_zero, fact_one_apply, ite_eq_right h, mul_zero]
      · rw [zero_mul]
  | succ m ih =>
    rw [pow_succ', hF.kingmanGenerator_mul_apply, ih hF]
    have hmerge : ∀ F' ∈ merges F, (kingmanGenerator ^ m) F' G =
        deathPow m (#(roots F) - 1) (#(roots G)) *
          (jumpMatrix ^ (#(roots F) - 1 - #(roots G))) F' G := fun F' hF' => by
      obtain ⟨hF'f, hcard, -⟩ := hF.of_mem_merges hF'
      rw [ih hF'f, show #(roots F') = #(roots F) - 1 by omega]
    rw [Finset.sum_congr rfl hmerge, ← Finset.mul_sum, deathPow_succ]
    by_cases hk : #(roots F) ≤ 1
    · have hC : (((#(roots F)).choose 2 : ℕ) : ℝ) = 0 := by
        rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
      rw [hC, merges_eq_empty_of_card_roots_le_one hk]; simp
    · replace hk : 2 ≤ #(roots F) := by omega
      by_cases hjk : #(roots G) < #(roots F)
      · have hstep := jumpMatrix_pow_succ_apply hk (#(roots F) - 1 - #(roots G)) G
        rw [show #(roots F) - 1 - #(roots G) + 1 = #(roots F) - #(roots G) by omega] at hstep
        have hC : (((#(roots F)).choose 2 : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.choose_pos hk).ne'
        rw [hstep]; field_simp; ring
      · rw [deathPow_eq_zero_of_lt (show #(roots F) - 1 < #(roots G) by omega)]; ring

theorem kingmanTransition_apply {F : Finset (Finset L)} (hF : IsForest F) (t : ℝ)
    (G : Finset (Finset L)) :
    kingmanTransition t F G =
      deathProb (#(roots F)) (#(roots G)) t * (jumpMatrix ^ (#(roots F) - #(roots G))) F G := by
  refine (fact_hasSum_exp_apply (t • kingmanGenerator (L := L)) F G).unique ?_
  convert (hasSum_deathProb (#(roots F)) (#(roots G)) t).mul_right
    ((jumpMatrix ^ (#(roots F) - #(roots G))) F G) using 1
  funext n
  rw [smul_pow, Matrix.smul_apply, kingmanGenerator_pow_apply hF, smul_eq_mul]; ring

theorem kingmanTransition_add (s t : ℝ) :
    kingmanTransition (L := L) (s + t) = kingmanTransition s * kingmanTransition t := by
  unfold kingmanTransition
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left s).smul_right t)

theorem kingmanTransition_of_card_roots_le_one {F : Finset (Finset L)} (hF : IsForest F)
    (hk : #(roots F) ≤ 1) (t : ℝ) (G : Finset (Finset L)) :
    kingmanTransition t F G = if G = F then 1 else 0 := by
  rw [kingmanTransition_apply hF]
  by_cases hG : G = F
  · subst hG
    rw [Nat.sub_self, pow_zero, Matrix.one_apply_eq, mul_one, ite_eq_left rfl, deathProb_self,
      Nat.choose_eq_zero_of_lt (by omega : #(roots G) < 2)]
    simp
  · rw [jumpMatrix_pow_of_card_roots_le_one hk, ite_eq_right hG, mul_zero]

theorem kingmanTransition_nonneg {t : ℝ} (ht : 0 ≤ t) (F G : Finset (Finset L)) :
    0 ≤ kingmanTransition t F G := by
  set Q := kingmanGenerator (L := L) with hQ
  set c : ℝ := ∑ F : Finset (Finset L), (((#(roots F)).choose 2 : ℕ) : ℝ)
  set P : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ := Q + c • 1 with hPdef
  have hP : ∀ F G, 0 ≤ P F G := fun F G => by
    rw [hPdef, Matrix.add_apply, Matrix.smul_apply, fact_one_apply, smul_eq_mul, hQ]
    unfold kingmanGenerator
    by_cases h : G = F
    · subst h
      simp only [ite_true, mul_one]
      have : (((#(roots G)).choose 2 : ℕ) : ℝ) ≤ c :=
        Finset.single_le_sum (f := fun F : Finset (Finset L) => (((#(roots F)).choose 2 : ℕ) : ℝ))
          (fun _ _ => by positivity) (Finset.mem_univ G)
      linarith
    · simp only [ite_eq_right h, mul_zero, add_zero]; split_ifs <;> norm_num
  have hPn : ∀ n F G, 0 ≤ (P ^ n) F G := fun n => by
    induction n with
    | zero => intro F G; rw [pow_zero, fact_one_apply]; split_ifs <;> norm_num
    | succ n ih =>
      intro F G; rw [pow_succ', Matrix.mul_apply]
      exact Finset.sum_nonneg fun F' _ => mul_nonneg (hP F F') (ih F' G)
  have hexpP : ∀ F G, 0 ≤ NormedSpace.exp (t • P) F G := fun F G => by
    refine (fact_hasSum_exp_apply (t • P) F G).nonneg fun n => ?_
    rw [smul_pow, Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg ht n) (hPn n F G))
  have hscal : ∀ (r : ℝ) (F G : Finset (Finset L)), 0 ≤
      NormedSpace.exp (r • (1 : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ)) F G := by
    intro r F G
    have h := fact_hasSum_exp_apply
      (r • (1 : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ)) F G
    simp_rw [smul_pow, one_pow, Matrix.smul_apply, fact_one_apply, smul_eq_mul] at h
    by_cases hGF : G = F
    · simp only [ite_eq_left hGF, mul_one] at h
      rw [h.unique (by convert fact_hasSum_exp_mul 1 r using 1; funext n; ring)]
      positivity
    · simp only [ite_eq_right hGF, mul_zero] at h
      rw [h.unique hasSum_zero]
  have hsplit : t • Q =
      t • P + (-(t * c)) • (1 : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ) := by
    rw [hPdef, smul_add, smul_smul, add_assoc, ← add_smul]; simp
  show 0 ≤ NormedSpace.exp (t • Q) F G
  rw [hsplit, Matrix.exp_add_of_commute _ _ ((Commute.one_right _).smul_right _), Matrix.mul_apply]
  exact Finset.sum_nonneg fun F' _ => mul_nonneg (hexpP F F') (hscal _ F' G)

private theorem fact_sum_kingmanGenerator_pow {F : Finset (Finset L)} (hF : IsForest F) (n : ℕ) :
    ∑ G, (kingmanGenerator ^ n) F G = if n = 0 then 1 else 0 := by
  induction n generalizing F with
  | zero => simp [fact_one_apply]
  | succ n ih =>
    simp_rw [pow_succ', Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [hF.sum_kingmanGenerator_mul, ih hF,
      Finset.sum_congr rfl (fun F' hF' => ih (hF.of_mem_merges hF').1),
      Finset.sum_const, hF.card_merges, nsmul_eq_mul, ite_eq_right (Nat.succ_ne_zero n)]
    ring

theorem kingmanTransition_sum {F : Finset (Finset L)} (hF : IsForest F) (t : ℝ) :
    ∑ G, kingmanTransition t F G = 1 := by
  refine (hasSum_sum (s := univ) fun G _ =>
    fact_hasSum_exp_apply (t • kingmanGenerator (L := L)) F G).unique ?_
  convert hasSum_ite_eq 0 (1 : ℝ) using 1
  funext n
  simp_rw [smul_pow, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← Finset.mul_sum]
  rw [fact_sum_kingmanGenerator_pow hF]
  split_ifs with hn <;> simp [hn]

theorem deathProb_eq_zero_of_lt {k j : ℕ} (h : k < j) (t : ℝ) : deathProb k j t = 0 := by
  simp [deathProb, deathPow_eq_zero_of_lt h]

private def dLin (a b c d : ℝ) (m : ℕ) : ℝ :=
  a * 0 ^ m + b * (-1) ^ m + c * (-3) ^ m + d * (-6) ^ m

private theorem fact_deathProb_of_closed {k j : ℕ} {a b c d : ℝ}
    (h : ∀ m, deathPow m k j = dLin a b c d m) (t : ℝ) :
    deathProb k j t = a + b * exp (-t) + c * exp (-t) ^ 3 + d * exp (-t) ^ 6 := by
  have hs := (((fact_hasSum_exp_mul 0 t).mul_left a).add
    ((fact_hasSum_exp_mul (-1) t).mul_left b)).add ((fact_hasSum_exp_mul (-3) t).mul_left c)
      |>.add ((fact_hasSum_exp_mul (-6) t).mul_left d)
  have e : deathProb k j t =
      a * exp (0 * t) + b * exp (-1 * t) + c * exp (-3 * t) + d * exp (-6 * t) :=
    HasSum.tsum_eq (by convert hs using 1; funext m; rw [h m, dLin]; ring)
  have e3 : exp (-3 * t) = exp (-t) ^ 3 := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have e6 : exp (-6 * t) = exp (-t) ^ 6 := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  rw [e, zero_mul, Real.exp_zero, neg_one_mul, e3, e6]; ring

private theorem fact_dLin_rec {k j : ℕ} (a b c d : ℝ)
    (h0 : (if k = j then (1 : ℝ) else 0) = a + b + c + d := by norm_num)
    (hs : ∀ m, ((k.choose 2 : ℕ) : ℝ) * (deathPow m (k - 1) j - dLin a b c d m) =
      dLin a b c d (m + 1)) (m : ℕ) : deathPow m k j = dLin a b c d m := by
  induction m with
  | zero => simpa [deathPow, dLin] using h0
  | succ m ih => rw [deathPow_succ, ih, hs]

private theorem fact_deathPow_two_one : ∀ m, deathPow m 2 1 = dLin 1 (-1) 0 0 m :=
  fact_dLin_rec 1 (-1) 0 0 (hs := fun m => by
    rw [show (2 : ℕ) - 1 = 1 from rfl, deathPow_self]; simp [dLin, pow_succ, Nat.choose])

private theorem fact_deathPow_three_two : ∀ m, deathPow m 3 2 = dLin 0 (3 / 2) (-3 / 2) 0 m :=
  fact_dLin_rec 0 (3 / 2) (-3 / 2) 0 (hs := fun m => by
    rw [show (3 : ℕ) - 1 = 2 from rfl, deathPow_self]; simp [dLin, pow_succ, Nat.choose]; ring)

private theorem fact_deathPow_three_one : ∀ m, deathPow m 3 1 = dLin 1 (-3 / 2) (1 / 2) 0 m :=
  fact_dLin_rec 1 (-3 / 2) (1 / 2) 0 (hs := fun m => by
    rw [show (3 : ℕ) - 1 = 2 from rfl, fact_deathPow_two_one]
    simp only [dLin, pow_succ, zero_pow (Nat.succ_ne_zero m), Nat.choose]; push_cast; ring)

theorem deathProb_small (t : ℝ) :
    let T := exp (-t)
    deathProb 0 0 t = 1 ∧ deathProb 1 1 t = 1 ∧
    deathProb 2 1 t = 1 - T ∧ deathProb 2 2 t = T ∧
    deathProb 3 1 t = 1 - 3 / 2 * T + 1 / 2 * T ^ 3 ∧ deathProb 3 2 t = 3 / 2 * T - 3 / 2 * T ^ 3 ∧
      deathProb 3 3 t = T ^ 3 ∧
    deathProb 4 1 t = 1 - 9 / 5 * T + T ^ 3 - 1 / 5 * T ^ 6 ∧
      deathProb 4 2 t = 9 / 5 * T - 3 * T ^ 3 + 6 / 5 * T ^ 6 ∧
      deathProb 4 3 t = 2 * T ^ 3 - 2 * T ^ 6 ∧ deathProb 4 4 t = T ^ 6 := by
  intro T
  have hT3 : exp (-(((Nat.choose 3 2 : ℕ) : ℝ) * t)) = T ^ 3 := by
    rw [← Real.exp_nat_mul, show Nat.choose 3 2 = 3 from rfl]; push_cast; ring_nf
  have hT6 : exp (-(((Nat.choose 4 2 : ℕ) : ℝ) * t)) = T ^ 6 := by
    rw [← Real.exp_nat_mul, show Nat.choose 4 2 = 6 from rfl]; push_cast; ring_nf
  refine ⟨by rw [deathProb_self]; simp, by rw [deathProb_self]; simp,
    by rw [fact_deathProb_of_closed fact_deathPow_two_one]; ring,
    by rw [deathProb_self, show Nat.choose 2 2 = 1 from rfl]; simp [T],
    by rw [fact_deathProb_of_closed fact_deathPow_three_one]; ring,
    by rw [fact_deathProb_of_closed fact_deathPow_three_two]; ring,
    by rw [deathProb_self, hT3],
    by rw [fact_deathProb_of_closed (fact_dLin_rec 1 (-9 / 5) 1 (-1 / 5) (hs := fun m => by
        rw [show (4 : ℕ) - 1 = 3 from rfl, fact_deathPow_three_one]
        simp only [dLin, pow_succ, zero_pow (Nat.succ_ne_zero m), Nat.choose]; push_cast; ring))]; ring,
    by rw [fact_deathProb_of_closed (fact_dLin_rec 0 (9 / 5) (-3) (6 / 5) (hs := fun m => by
        rw [show (4 : ℕ) - 1 = 3 from rfl, fact_deathPow_three_two]
        simp [dLin, pow_succ, Nat.choose]; ring))]; ring,
    by rw [fact_deathProb_of_closed (fact_dLin_rec 0 0 2 (-2) (hs := fun m => by
        rw [show (4 : ℕ) - 1 = 3 from rfl, deathPow_self]
        simp [dLin, pow_succ, Nat.choose]; ring))]; ring,
    by rw [deathProb_self, hT6]⟩

open Filter Topology

private theorem absorb_deathPow_zero (m k : ℕ) (hk : 1 ≤ k) : deathPow m k 0 = 0 := by
  induction m generalizing k with
  | zero => simp only [deathPow]; rw [ite_eq_right (by omega)]
  | succ m ih =>
    simp only [deathPow]
    rcases Nat.lt_or_ge k 2 with h | h
    · obtain rfl : k = 1 := by omega
      simp
    · rw [ih (k - 1) (by omega), ih k hk, sub_self, mul_zero]

private theorem absorb_spectral (k j : ℕ) (hk : 1 ≤ k) :
    ∃ c : ℕ → ℝ, c 1 = (if j = 1 then 1 else 0) ∧
      ∀ m, deathPow m k j = ∑ r ∈ Icc 1 k, c r * (-(((r.choose 2 : ℕ) : ℝ))) ^ m := by
  induction k, hk using Nat.le_induction with
  | base =>
    refine ⟨fun _ => if j = 1 then 1 else 0, rfl, fun m => ?_⟩
    rw [Icc_self, sum_singleton, show Nat.choose 1 2 = 0 from rfl, Nat.cast_zero, neg_zero]
    cases m <;> simp [deathPow, eq_comm]
  | succ k hk ih =>
    obtain ⟨c, hc1, ih⟩ := ih
    let a : ℝ := (((k + 1).choose 2 : ℕ) : ℝ)
    let d : ℕ → ℝ := fun r => a / (a - ((r.choose 2 : ℕ) : ℝ)) * c r
    let c' : ℕ → ℝ := fun r =>
      if r = k + 1 then (if k + 1 = j then 1 else 0) - ∑ s ∈ Icc 1 k, d s else d r
    have ha : 0 < a := Nat.cast_pos.2 (Nat.choose_pos (by omega : 2 ≤ k + 1))
    have hlt : ∀ r ∈ Icc 1 k, (((r.choose 2 : ℕ) : ℝ)) < a := fun r hr => by
      have hle : r.choose 2 ≤ k.choose 2 := Nat.choose_le_choose 2 (mem_Icc.1 hr).2
      have hsucc : (k + 1).choose 2 = k + k.choose 2 := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
      exact Nat.cast_lt.2 (by omega : r.choose 2 < (k + 1).choose 2)
    have hcr : ∀ r ∈ Icc 1 k, a * (c r - c' r) = c' r * (-(((r.choose 2 : ℕ) : ℝ))) := fun r hr => by
      have hne : r ≠ k + 1 := by have := (mem_Icc.1 hr).2; omega
      have hsub : a - ((r.choose 2 : ℕ) : ℝ) ≠ 0 := sub_ne_zero.2 (hlt r hr).ne'
      simp only [c', ite_eq_right hne, d]; field_simp; ring
    refine ⟨c', ?_, fun m => ?_⟩
    · simp only [c', ite_eq_right (by omega : 1 ≠ k + 1), d, show Nat.choose 1 2 = 0 from rfl,
        Nat.cast_zero, sub_zero, div_self ha.ne', one_mul, hc1]
    · induction m with
      | zero =>
        have hsum : ∑ r ∈ Icc 1 k, c' r = ∑ r ∈ Icc 1 k, d r :=
          sum_congr rfl fun r hr => by
            simp only [c', ite_eq_right (by have := (mem_Icc.1 hr).2; omega : r ≠ k + 1)]
        rw [sum_Icc_succ_top (by omega)]
        simp only [pow_zero, mul_one, deathPow, hsum, c', ite_true]; ring
      | succ m ihm =>
        rw [deathPow_succ, Nat.add_sub_cancel, ih m, ihm, sum_Icc_succ_top (by omega),
          sum_Icc_succ_top (by omega)]
        have hstep : a * (∑ r ∈ Icc 1 k, c r * (-(((r.choose 2 : ℕ) : ℝ))) ^ m -
            (∑ r ∈ Icc 1 k, c' r * (-(((r.choose 2 : ℕ) : ℝ))) ^ m + c' (k + 1) * (-a) ^ m)) =
            (∑ r ∈ Icc 1 k, a * (c r - c' r) * (-(((r.choose 2 : ℕ) : ℝ))) ^ m) +
              c' (k + 1) * (-a) ^ (m + 1) := by
          rw [sub_add_eq_sub_sub, mul_sub, ← sum_sub_distrib, mul_sum,
            sum_congr rfl (fun r _ => by ring : ∀ r ∈ Icc 1 k,
              a * (c r * (-(((r.choose 2 : ℕ) : ℝ))) ^ m - c' r * (-(((r.choose 2 : ℕ) : ℝ))) ^ m) =
                a * (c r - c' r) * (-(((r.choose 2 : ℕ) : ℝ))) ^ m), pow_succ']
          ring
        rw [hstep]
        congr 1
        refine sum_congr rfl fun r hr => ?_
        rw [hcr r hr, pow_succ', mul_assoc]

theorem tendsto_deathProb (k j : ℕ) (hk : 1 ≤ k) :
    Tendsto (deathProb k j) atTop (𝓝 (if j = 1 then 1 else 0)) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h : deathProb k 0 = fun _ => 0 := funext fun t => by
      simp [deathProb, absorb_deathPow_zero _ _ hk]
    rw [h, ite_eq_right (by norm_num)]
    exact tendsto_const_nhds
  obtain ⟨c, hc1, hpow⟩ := absorb_spectral k j hk
  have hprob : ∀ t, deathProb k j t =
      ∑ r ∈ Icc 1 k, exp (-(((r.choose 2 : ℕ) : ℝ) * t)) * c r := fun t => by
    have key : ∀ r ∈ Icc 1 k, HasSum (fun m : ℕ => t ^ m / (m.factorial : ℝ) *
        (c r * (-(((r.choose 2 : ℕ) : ℝ))) ^ m))
        (exp (-(((r.choose 2 : ℕ) : ℝ) * t)) * c r) := fun r _ => by
      rw [← neg_mul]
      convert (fact_hasSum_exp_mul (-(((r.choose 2 : ℕ) : ℝ))) t).mul_right (c r) using 1
      funext m; ring
    unfold deathProb
    rw [← (hasSum_sum key).tsum_eq]
    congr 1; funext m; rw [hpow m, mul_sum]
  rw [funext hprob]
  have hlim : (if j = 1 then (1 : ℝ) else 0) =
      ∑ r ∈ Icc 1 k, (if r = 1 then (1 : ℝ) else 0) * c r := by
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_Icc, le_refl, hk, and_self, ite_true,
      hc1]
  rw [hlim]
  refine tendsto_finsetSum _ fun r hr => Tendsto.mul_const _ ?_
  split_ifs with h
  · subst h; simp
  · have hpos : (0 : ℝ) < ((r.choose 2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by have := (mem_Icc.1 hr).1; omega)
    exact tendsto_exp_comp_nhds_zero.mpr
      (tendsto_neg_atTop_atBot.comp (Tendsto.const_mul_atTop hpos tendsto_id))

private theorem absorb_tendsto {F : Finset (Finset L)} (hF : IsForest F)
    (G : Finset (Finset L)) :
    Tendsto (fun t => kingmanTransition t F G) atTop
      (𝓝 (if #(roots F) = 0 then (if G = F then 1 else 0)
        else if #(roots G) = 1 then (jumpMatrix ^ (#(roots F) - 1)) F G else 0)) := by
  rcases Nat.eq_zero_or_pos (#(roots F)) with h0 | hpos
  · rw [ite_eq_left h0, show (fun t => kingmanTransition t F G) = fun _ => if G = F then 1 else 0
      from funext fun t => kingmanTransition_of_card_roots_le_one hF (by omega) t G]
    exact tendsto_const_nhds
  · rw [ite_eq_right (by omega), show (fun t => kingmanTransition t F G) = fun t =>
      deathProb (#(roots F)) (#(roots G)) t * (jumpMatrix ^ (#(roots F) - #(roots G))) F G
      from funext fun t => kingmanTransition_apply hF t G]
    have hl := (tendsto_deathProb (#(roots F)) (#(roots G)) hpos).mul_const
      ((jumpMatrix ^ (#(roots F) - #(roots G))) F G)
    split_ifs at hl ⊢ with hG
    · rw [hG] at hl ⊢; simpa using hl
    · simpa using hl

theorem tendsto_kingmanTransition {F : Finset (Finset L)} (hF : IsForest F)
    (G : Finset (Finset L)) :
    Tendsto (fun t => kingmanTransition t F G) atTop (𝓝 (kingmanAbsorption F G)) := by
  have h := absorb_tendsto hF G
  have e : kingmanAbsorption F G = _ := h.limUnder_eq
  rwa [e]

theorem kingmanAbsorption_apply {F : Finset (Finset L)} (hF : IsForest F)
    (G : Finset (Finset L)) :
    kingmanAbsorption F G =
      if #(roots F) = 0 then (if G = F then 1 else 0)
      else if #(roots G) = 1 then (jumpMatrix ^ (#(roots F) - 1)) F G else 0 :=
  (absorb_tendsto hF G).limUnder_eq

theorem kingmanAbsorption_nonneg {F : Finset (Finset L)} (hF : IsForest F)
    (G : Finset (Finset L)) : 0 ≤ kingmanAbsorption F G := by
  rw [kingmanAbsorption_apply hF]
  split_ifs
  · exact zero_le_one
  · exact le_rfl
  · exact jumpMatrix_pow_nonneg _ _ _
  · exact le_rfl

theorem kingmanAbsorption_sum {F : Finset (Finset L)} (hF : IsForest F) :
    ∑ G, kingmanAbsorption F G = 1 := by
  have h1 : Tendsto (fun t => ∑ G, kingmanTransition t F G) atTop
      (𝓝 (∑ G, kingmanAbsorption F G)) :=
    tendsto_finsetSum _ fun G _ => tendsto_kingmanTransition hF G
  rw [show (fun t => ∑ G, kingmanTransition t F G) = fun _ => 1 from
    funext fun t => kingmanTransition_sum hF t] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

theorem kingmanAbsorption_first_step {F : Finset (Finset L)} (hF : IsForest F)
    (hk : 2 ≤ #(roots F)) (G : Finset (Finset L)) :
    kingmanAbsorption F G =
      (((#(roots F)).choose 2 : ℕ) : ℝ)⁻¹ * ∑ F' ∈ merges F, kingmanAbsorption F' G := by
  rw [kingmanAbsorption_apply hF, ite_eq_right (by omega)]
  have hm : ∀ F' ∈ merges F, kingmanAbsorption F' G =
      if #(roots G) = 1 then (jumpMatrix ^ (#(roots F) - 2)) F' G else 0 := fun F' hF' => by
    obtain ⟨hF'f, hcard, -⟩ := hF.of_mem_merges hF'
    rw [kingmanAbsorption_apply hF'f, ite_eq_right (by omega),
      show #(roots F') - 1 = #(roots F) - 2 by omega]
  rw [Finset.sum_congr rfl hm]
  split_ifs with hG
  · rw [show #(roots F) - 1 = (#(roots F) - 2) + 1 by omega, jumpMatrix_pow_succ_apply hk]
  · simp

theorem kingmanTransition_mul_kingmanAbsorption {F : Finset (Finset L)} (hF : IsForest F)
    (t : ℝ) (G : Finset (Finset L)) :
    ∑ F', kingmanTransition t F F' * kingmanAbsorption F' G = kingmanAbsorption F G := by
  have hlim : Tendsto (fun s => kingmanTransition (t + s) F G) atTop
      (𝓝 (kingmanAbsorption F G)) :=
    (tendsto_kingmanTransition hF G).comp (tendsto_atTop_add_const_left atTop t tendsto_id)
  rw [show (fun s => kingmanTransition (t + s) F G) =
    fun s => ∑ F', kingmanTransition t F F' * kingmanTransition s F' G from
    funext fun s => by rw [kingmanTransition_add, Matrix.mul_apply]] at hlim
  refine tendsto_nhds_unique (tendsto_finsetSum _ fun F' _ => ?_) hlim
  by_cases h : kingmanTransition t F F' = 0
  · simp only [h, zero_mul]; exact tendsto_const_nhds
  · rw [kingmanTransition_apply hF] at h
    exact (tendsto_kingmanTransition (jumpMatrix_pow_support hF (right_ne_zero_of_mul h)).1 G).const_mul _

noncomputable def unrootedOutcome (F T : Finset (Finset L)) : ℝ :=
  ∑ G, if unroot G = T then kingmanAbsorption F G else 0

theorem absorb_mem_unroot {G : Finset (Finset L)} {A : Finset L} :
    A ∈ unroot G ↔ (A ∈ G ∧ A ≠ univ) ∨ (Aᶜ ∈ G ∧ Aᶜ ≠ univ) := by
  unfold unroot
  simp only [mem_union, mem_erase, mem_image]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨B, ⟨h1, h2⟩, rfl⟩)
    · exact Or.inl ⟨h2, h1⟩
    · rw [compl_compl]; exact Or.inr ⟨h2, h1⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨Aᶜ, ⟨h2, h1⟩, compl_compl A⟩

theorem absorb_unroot_insert_univ (F : Finset (Finset L)) : unroot (insert univ F) = unroot F := by
  unfold unroot; rw [erase_insert_eq_erase]

theorem absorb_unroot_insert_of_mem {F : Finset (Finset L)} {D : Finset L} (hD : D ∈ unroot F) :
    unroot (insert D F) = unroot F := by
  rw [absorb_mem_unroot] at hD
  ext A
  rw [absorb_mem_unroot, absorb_mem_unroot, mem_insert, mem_insert]
  constructor
  · rintro (⟨rfl | h, hne⟩ | ⟨h | h, hne⟩)
    · exact hD
    · exact Or.inl ⟨h, hne⟩
    · subst h
      rcases hD with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
      · rw [compl_compl] at h1 h2; exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h, hne⟩
  · rintro (⟨h, hne⟩ | ⟨h, hne⟩)
    · exact Or.inl ⟨Or.inr h, hne⟩
    · exact Or.inr ⟨Or.inr h, hne⟩

theorem absorb_merges_of_card_roots_eq_two {F G : Finset (Finset L)}
    (hcov : lineages F = univ) (h₂ : #(roots F) = 2) (hG : G ∈ merges F) :
    G = insert univ F := by
  obtain ⟨A, hA, B, hB, hAB, rfl⟩ := mem_merges.1 hG
  have hroots : roots F = {A, B} := (eq_of_subset_of_card_le
    (by simp [insert_subset_iff, hA, hB]) (by rw [h₂, card_pair hAB])).symm
  have hunion : A ∪ B = univ := by rw [← hcov, ← lineages_roots, hroots]; simp [lineages]
  rw [hunion]

theorem absorb_union_mem_unroot {F : Finset (Finset L)} (hF : IsForest F)
    (hcov : lineages F = univ) (h₃ : #(roots F) = 3) {A B : Finset L} (hA : A ∈ roots F)
    (hB : B ∈ roots F) (hAB : A ≠ B) : A ∪ B ∈ unroot F := by
  obtain ⟨C, hC⟩ := card_eq_one.1 (by
    rw [card_erase_of_mem (mem_erase.2 ⟨hAB.symm, hB⟩), card_erase_of_mem hA, h₃] :
      #(((roots F).erase A).erase B) = 1)
  have hCmem : C ∈ ((roots F).erase A).erase B := hC ▸ mem_singleton_self C
  simp only [mem_erase] at hCmem
  obtain ⟨hCB, hCA, hCr⟩ := hCmem
  have hroots : roots F = insert A {B, C} := (eq_of_subset_of_card_le
    (by simp [insert_subset_iff, hA, hB, hCr])
    (by rw [h₃, card_insert_of_notMem (by simp [hAB, Ne.symm hCA]), card_pair hCB.symm])).symm
  have hunion : A ∪ (B ∪ C) = univ := by rw [← hcov, ← lineages_roots, hroots]; simp [lineages]
  have hdisjA : Disjoint C A := hF.disjoint_of_mem_roots hCr hA hCA
  have hdisjB : Disjoint C B := hF.disjoint_of_mem_roots hCr hB hCB
  have hcompl : (A ∪ B)ᶜ = C := by
    ext x; simp only [mem_compl, mem_union, not_or]
    refine ⟨fun ⟨hxA, hxB⟩ => ?_, fun hxC =>
      ⟨disjoint_left.1 hdisjA hxC, disjoint_left.1 hdisjB hxC⟩⟩
    have hx : x ∈ A ∪ (B ∪ C) := hunion.symm ▸ mem_univ x
    simp only [mem_union] at hx; tauto
  rw [absorb_mem_unroot, hcompl]
  refine Or.inr ⟨roots_subset F hCr, fun hCu => ?_⟩
  obtain ⟨a, ha⟩ := hF.1 A (roots_subset F hA)
  exact disjoint_left.1 hdisjA (hCu ▸ mem_univ a) ha

theorem absorb_unroot_eq_of_kingmanAbsorption_ne_zero {F : Finset (Finset L)} (hF : IsForest F)
    (hcov : lineages F = univ) (h₁ : 1 ≤ #(roots F)) (h₃ : #(roots F) ≤ 3)
    {G : Finset (Finset L)} (hG : kingmanAbsorption F G ≠ 0) : unroot G = unroot F := by
  rw [kingmanAbsorption_apply hF, ite_eq_right (by omega)] at hG
  split_ifs at hG with hG1
  swap
  · exact absurd rfl hG
  obtain h | h | h : #(roots F) = 1 ∨ #(roots F) = 2 ∨ #(roots F) = 3 := by omega
  · rw [h, Nat.sub_self, pow_zero, Matrix.one_apply] at hG
    split_ifs at hG with hFG
    · rw [hFG]
    · exact absurd rfl hG
  · rw [h, show 2 - 1 = 1 from rfl, pow_one, jumpMatrix_apply_of_isForest (by omega)] at hG
    split_ifs at hG with hm
    · rw [absorb_merges_of_card_roots_eq_two hcov h hm, absorb_unroot_insert_univ]
    · exact absurd rfl hG
  · rw [h, show 3 - 1 = 1 + 1 from rfl, jumpMatrix_pow_succ_apply (by omega)] at hG
    obtain ⟨F', hF', hne⟩ := exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hG)
    obtain ⟨hF'f, hcard, -, -, hlin⟩ := hF.of_mem_merges hF'
    rw [pow_one, jumpMatrix_apply_of_isForest (by omega)] at hne
    split_ifs at hne with hm
    · rw [absorb_merges_of_card_roots_eq_two (hlin.trans hcov) (by omega) hm,
        absorb_unroot_insert_univ]
      obtain ⟨A, hA, B, hB, hAB, rfl⟩ := mem_merges.1 hF'
      exact absorb_unroot_insert_of_mem (absorb_union_mem_unroot hF hcov h hA hB hAB)
    · exact absurd rfl hne

theorem unrootedOutcome_of_card_roots_le_three {F : Finset (Finset L)} (hF : IsForest F)
    (hcov : lineages F = univ) (h₁ : 1 ≤ #(roots F)) (h₃ : #(roots F) ≤ 3)
    (T : Finset (Finset L)) :
    unrootedOutcome F T = if unroot F = T then 1 else 0 := by
  unfold unrootedOutcome
  have h : ∀ G, (if unroot G = T then kingmanAbsorption F G else 0) =
      if unroot F = T then kingmanAbsorption F G else 0 := fun G => by
    by_cases h0 : kingmanAbsorption F G = 0
    · simp [h0]
    · rw [absorb_unroot_eq_of_kingmanAbsorption_ne_zero hF hcov h₁ h₃ h0]
  rw [sum_congr rfl fun G _ => h G]
  split_ifs
  · exact kingmanAbsorption_sum hF
  · simp

theorem unrootedOutcome_first_step {F : Finset (Finset L)} (hF : IsForest F)
    (hk : 2 ≤ #(roots F)) (T : Finset (Finset L)) :
    unrootedOutcome F T =
      (((#(roots F)).choose 2 : ℕ) : ℝ)⁻¹ * ∑ F' ∈ merges F, unrootedOutcome F' T := by
  unfold unrootedOutcome
  have h : ∀ G, (if unroot G = T then kingmanAbsorption F G else 0) =
      ∑ F' ∈ merges F, (((#(roots F)).choose 2 : ℕ) : ℝ)⁻¹ *
        (if unroot G = T then kingmanAbsorption F' G else 0) := fun G => by
    rw [kingmanAbsorption_first_step hF hk G, ← mul_sum]
    by_cases hT : unroot G = T <;> simp [hT]
  rw [sum_congr rfl fun G _ => h G, sum_comm, mul_sum]
  exact sum_congr rfl fun F' _ => by rw [mul_sum]

end ADR11
