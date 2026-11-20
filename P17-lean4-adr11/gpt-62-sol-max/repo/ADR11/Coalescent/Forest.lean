module

public import ADR11.Defs

/-! The roots of a forest partition its lineages, and merging two roots preserves the forest. -/

@[expose] public section

namespace ADR11

open Finset

/-- A family of leaf clusters, used for forests, hierarchies, and split systems. -/
abbrev ClusterFamily (L : Type*) := Finset (Finset L)

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- A forest: nonempty clusters, any two of which are nested or disjoint. -/
def IsForest (F : ClusterFamily L) : Prop :=
  (∀ A ∈ F, A.Nonempty) ∧ ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

/-- The lineages of a forest: the union of its clusters. -/
def lineages (F : ClusterFamily L) : Finset L :=
  F.sup id

theorem mem_roots {F : ClusterFamily L} {A : Finset L} :
    A ∈ roots F ↔ A ∈ F ∧ ∀ B ∈ F, A ⊆ B → B = A := mem_filter

theorem roots_subset (F : ClusterFamily L) : roots F ⊆ F :=
  filter_subset _ _

/-! ### Lineages -/

section Lineages

omit [Fintype L]

theorem subset_lineages {F : ClusterFamily L} {A : Finset L} (hA : A ∈ F) :
    A ⊆ lineages F :=
  le_sup (f := id) hA

@[simp] theorem lineages_singleton (A : Finset L) : lineages {A} = A :=
  sup_singleton

@[simp] theorem lineages_insert (A : Finset L) (F : ClusterFamily L) :
    lineages (insert A F) = A ∪ lineages F :=
  sup_insert

end Lineages

/-- Join the roots in `P` in a new cluster above `F`. -/
def mergeAt (F P : ClusterFamily L) := insert (lineages P) F

/-- The unordered pairs of roots. Each such pair merges at rate one. -/
abbrev mergePairs (F : ClusterFamily L) := (roots F).powersetCard 2

/-- Total coalescence rate with `k` lineages. -/
def rate (k : ℕ) : ℝ := k.choose 2

@[simp] theorem rate_one : rate 1 = 0 := by norm_num [rate]
@[simp] theorem rate_eq_zero {k : ℕ} : rate k = 0 ↔ k ≤ 1 := by
  simp [rate, Nat.choose_eq_zero_iff]

theorem rate_pos {k : ℕ} (h : 2 ≤ k) : 0 < rate k := Nat.cast_pos.2 (Nat.choose_pos h)

private theorem mem_merge_image {F G : ClusterFamily L} :
    G ∈ (mergePairs F).image (mergeAt F) ↔ ∃ A ∈ roots F, ∃ B ∈ roots F, A ≠ B ∧ G = insert (A ∪ B) F := by
  simp only [mem_image, mem_powersetCard, card_eq_two]
  constructor
  · rintro ⟨_, ⟨hp, A, B, hab, rfl⟩, rfl⟩
    exact ⟨A, hp (by simp), B, hp (by simp), hab, by simp [mergeAt]⟩
  · rintro ⟨A, ha, B, hb, hab, rfl⟩
    exact ⟨{A, B}, ⟨by grind, A, B, hab, rfl⟩, by simp [mergeAt]⟩

/-! ### Roots and merges of forests -/

/-- Every cluster lies below a maximal one (for any finite family of clusters). -/
theorem exists_mem_roots_subset {F : ClusterFamily L} {A : Finset L}
    (hA : A ∈ F) : ∃ R ∈ roots F, A ⊆ R := by
  obtain ⟨R, hAR, hR, hmax⟩ := F.exists_le_maximal hA
  exact ⟨R, mem_roots.2 ⟨hR, fun B hB h => (hmax hB h).antisymm h⟩, hAR⟩

theorem IsForest.disjoint_of_mem_roots {F : ClusterFamily L} (hF : IsForest F) :
    (roots F : Set (Finset L)).PairwiseDisjoint id := by
  have := hF.2
  grind [Set.PairwiseDisjoint, Set.Pairwise, mem_roots]

private theorem disjoint_join {F P : ClusterFamily L} (hF : IsForest F) (hP : P ⊆ roots F)
    {R : Finset L} (hR : R ∈ roots F) (h : R ∉ P) : Disjoint R (lineages P) :=
  Finset.disjoint_sup_right.2 fun _ hQ => hF.disjoint_of_mem_roots hR (hP hQ) (ne_of_mem_of_not_mem hQ h).symm

private theorem join_no_superset {F P : ClusterFamily L} (hp : P ⊆ roots F) (hk : 2 ≤ #P)
    {C : Finset L} (hC : C ∈ F) : ¬ lineages P ⊆ C := by
  obtain ⟨A, ha, B, hb, hab⟩ := one_lt_card.1 hk
  intro h
  have key {R} (hR : R ∈ P) : C = R := (mem_roots.1 (hp hR)).2 C hC ((subset_lineages hR).trans h)
  exact hab ((key ha).symm.trans (key hb))

/-- A root lies below a union of roots precisely when it was selected. -/
private theorem filter_roots_join {F P : ClusterFamily L} (hF : IsForest F) (hP : P ⊆ roots F) :
    (roots F).filter (· ⊆ lineages P) = P := by
  ext R
  rw [mem_filter]
  refine ⟨fun ⟨hR, h⟩ => ?_, fun h => ⟨hP h, subset_lineages h⟩⟩
  by_contra hn
  exact (hF.1 R (roots_subset F hR)).ne_empty
    (disjoint_self.1 ((disjoint_join hF hP hR hn).mono_right h))

private theorem roots_insert {F : ClusterFamily L} {U : Finset L} (hU : ∀ C ∈ F, ¬ U ⊆ C) :
    roots (insert U F) = insert U ((roots F).filter fun C => ¬ C ⊆ U) := by
  grind [mem_roots]

theorem IsForest.mergeAt_inj {F : ClusterFamily L} (hF : IsForest F) :
    Set.InjOn (mergeAt F) (mergePairs F : ClusterFamily (Finset L)) := by
  intro P hp Q hq e
  obtain ⟨hp, hcp⟩ := mem_powersetCard.1 hp
  obtain ⟨hq, -⟩ := mem_powersetCard.1 hq
  rw [← filter_roots_join hF hp, ← filter_roots_join hF hq,
    (insert_inj (fun h => join_no_superset hp hcp.ge h Subset.rfl)).1 e]

/-- Merging a pair preserves the forest and its lineages, and removes one root. -/
theorem IsForest.merge_pair {F P : ClusterFamily L} (hF : IsForest F) (hp : P ∈ mergePairs F) :
    IsForest (mergeAt F P) ∧ #(roots (mergeAt F P)) + 1 = #(roots F) ∧ F ⊆ mergeAt F P ∧
      mergeAt F P ≠ F ∧ lineages (mergeAt F P) = lineages F := by
  obtain ⟨hp, hc⟩ := mem_powersetCard.1 hp
  have big (C) (hC : C ∈ F) := join_no_superset hp hc.ge hC
  have hn : lineages P ∉ F := by grind
  have forest : IsForest (mergeAt F P) := by
    obtain ⟨A, ha⟩ := card_pos.1 (by omega : 0 < #P)
    have hn' := (hF.1 A (roots_subset F (hp ha))).mono (subset_lineages ha)
    have key C (hC : C ∈ F) : C ⊆ lineages P ∨ Disjoint C (lineages P) := by
      obtain ⟨R, hR, le⟩ := exists_mem_roots_subset hC
      by_cases h : R ∈ P
      · exact Or.inl (le.trans (subset_lineages h))
      · exact Or.inr ((disjoint_join hF hp hR h).mono_left le)
    obtain ⟨hN, hl⟩ := hF
    simp only [mergeAt, IsForest, forall_mem_insert]
    grind [Disjoint.symm]
  refine ⟨forest, ?_, subset_insert _ _, fun e => hn (e ▸ mem_insert_self _ _),
    (lineages_insert ..).trans (union_eq_right.2 (sup_mono (hp.trans (roots_subset F))))⟩
  rw [mergeAt, roots_insert big, filter_not, filter_roots_join hF hp,
    card_insert_of_notMem (notMem_mono (sdiff_subset.trans (roots_subset F)) hn), card_sdiff_of_subset hp, hc]
  have := card_le_card hp
  omega

theorem IsForest.generator_preserves {F G : ClusterFamily L} (hF : IsForest F)
    (h : kingmanGenerator F G ≠ 0) : IsForest G := by
  simp only [kingmanGenerator, ← mem_merge_image] at h
  split_ifs at h with e hg
  · exact e ▸ hF
  · obtain ⟨P, hp, rfl⟩ := mem_image.1 hg
    exact (hF.merge_pair hp).1
  · contradiction

/-- The generator applied to a test function sums its changes over all pairs of roots. -/
theorem IsForest.sum_generator_pairs {F : ClusterFamily L} (hF : IsForest F)
    (u : ClusterFamily L → ℝ) :
    ∑ G, kingmanGenerator F G * u G = ∑ P ∈ mergePairs F, (u (mergeAt F P) - u F) := by
  have key (G : ClusterFamily L) : kingmanGenerator F G =
      (if G = F then -rate #(roots F) else 0) + (if G ∈ (mergePairs F).image (mergeAt F) then 1 else 0) := by
    have hn : F ∉ (mergePairs F).image (mergeAt F) := by
      simp only [mem_image, not_exists, not_and]
      intro P hp he
      exact (hF.merge_pair hp).2.2.2.1 he
    by_cases e : G = F <;> simp_all [kingmanGenerator, ← mem_merge_image, rate]
  simp only [key, add_mul, ite_mul, one_mul, zero_mul, sum_add_distrib, sum_ite_eq', mem_univ,
    ite_true, sum_ite_mem, univ_inter]
  rw [sum_image hF.mergeAt_inj, sum_sub_distrib, sum_const, nsmul_eq_mul, card_powersetCard]
  unfold rate
  ring

/-- Only the support of the weights matters when comparing weighted sums. -/
theorem sum_mul_congr {α : Type*} {s : Finset α} {p u v : α → ℝ}
    (h : ∀ a ∈ s, p a ≠ 0 → u a = v a) : ∑ a ∈ s, p a * u a = ∑ a ∈ s, p a * v a :=
  sum_congr rfl fun a ha => mul_eq_mul_left_iff.2 (or_iff_not_imp_right.2 (h a ha))

/-! ### Building forests -/

section Building

omit [Fintype L]

omit [DecidableEq L] in
theorem IsForest.subset {F G : ClusterFamily L} (hG : IsForest G) (h : F ⊆ G) : IsForest F :=
  ⟨fun A hA => hG.1 A (h hA), fun A hA B hB => hG.2 A (h hA) B (h hB)⟩

omit [DecidableEq L] in
theorem IsForest.image {M : Type*} [DecidableEq M] {F : ClusterFamily L} (hF : IsForest F)
    (f : Finset L → Finset M) (hn : ∀ A ∈ F, (f A).Nonempty) (hm : Monotone f)
    (hd : ∀ {A B}, Disjoint A B → Disjoint (f A) (f B)) : IsForest (F.image f) := by
  simp only [IsForest, forall_mem_image]
  exact ⟨hn, fun A ha B hb => (hF.2 A ha B hb).imp (fun h => hm h) (Or.imp (fun h => hm h) hd)⟩

/-- Adjoining singleton leaves preserves laminarity. -/
theorem IsForest.union_singletons {F : ClusterFamily L} (hF : IsForest F) (S : Finset L) :
    IsForest (F ∪ S.image (fun x => {x})) := by
  have := hF.1
  have := hF.2
  simp only [IsForest, forall_mem_union, forall_mem_image, singleton_nonempty]
  grind [disjoint_singleton_left, disjoint_singleton_right]

end Building

end ADR11
