module

public import ADR11.Clusters

/-! A merge inserts the union of two maximal, disjoint clades. Exactly
those two roots disappear; this both counts the jumps and identifies the
pair from its successor. -/

@[expose] public section

namespace ADR11

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]

@[simp] theorem joined_pair (F : Clusters L) (A B : Finset L) : joined F {A,B} = insert (A ∪ B) F := by simp [joined,lineages]

theorem mem_pairs {α : Type*} [DecidableEq α] {P R : Finset α} :
    P ∈ R.powersetCard 2 ↔ ∃ a ∈ R, ∃ b ∈ R, a ≠ b ∧ P = {a,b} := by
  grind [card_eq_two]

theorem mem_roots {F : Clusters L} {A : Finset L} :
    A ∈ roots F ↔ A ∈ F ∧ ∀ B ∈ F, A ⊆ B → B = A := mem_filter

theorem roots_subset (F : Clusters L) : roots F ⊆ F := filter_subset _ _

theorem mem_merges {F G : Clusters L} :
    G ∈ merges F ↔ ∃ A ∈ roots F, ∃ B ∈ roots F, A ≠ B ∧ G = insert (A ∪ B) F := by
  simp only [merges,mem_image,mem_pairs]; grind [joined_pair]

/-! ### Lineages -/

section Lineages

omit [Fintype L]

theorem mem_lineages {F : Clusters L} {l : L} : l ∈ lineages F ↔ ∃ A ∈ F, l ∈ A := by
  simp [lineages]

theorem subset_lineages {F : Clusters L} {A : Finset L} (hA : A ∈ F) :
    A ⊆ lineages F :=
  le_sup (f := id) hA

@[simp] theorem lineages_insert (A : Finset L) (F : Clusters L) :
    lineages (insert A F) = A ∪ lineages F :=
  sup_insert

end Lineages

/-! ### Roots and merges of forests -/

/-- Every cluster lies below a maximal one (for any finite family of clusters). -/
theorem exists_mem_roots_subset {F : Clusters L} {A : Finset L}
    (hA : A ∈ F) : ∃ R ∈ roots F, A ⊆ R := by
  obtain ⟨R, hAR, hR⟩ := F.exists_le_maximal hA
  exact ⟨R, mem_roots.2 ⟨hR.1, fun B hB hRB => le_antisymm (hR.2 hB hRB) hRB⟩, hAR⟩

theorem IsForest.disjoint_of_mem_roots {F : Clusters L} (hF : IsForest F) {A B : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hAB : A ≠ B) : Disjoint A B := by
  have := hF.2 A (roots_subset _ hA) B (roots_subset _ hB); grind [mem_roots]

/-- Strict inclusions between nonempty traces reflect strict inclusions of clades. -/
theorem IsForest.reflect_lt {Y : Type*} [Fintype Y] {s : Y → L} {F : Clusters L} (hf : IsForest F) {A B}
    (ha : A ∈ F) (hb : B ∈ F) (hn : (pre s A).Nonempty) (h : pre s A ⊂ pre s B) : A ⊂ B := by
  obtain ⟨y,hy⟩ := hn; have := hf.2 A ha B hb; have := h.subset hy
  grind [mem_pre,Finset.disjoint_left]

/-- Maximal clades project to maximal clades, omitting invisible roots. -/
theorem roots_project {L' : Type*} [Fintype L'] [DecidableEq L'] {F : Clusters L} (hf : IsForest F) (s : L' → L) : roots (project s F) = project s (roots F) := by
  ext D; rw [mem_roots,mem_project,mem_project]; constructor
  · rintro ⟨⟨hn,A,ha,rfl⟩,max⟩
    obtain ⟨B,hb,le⟩ := exists_mem_roots_subset ha
    have le := pre_mono s le; grind [project_mem,roots_subset,Finset.Nonempty]
  · rintro ⟨hn,A,ha,rfl⟩
    have refl := @IsForest.reflect_lt _ _ _ _ _ s F hf A
    grind [mem_roots,mem_project]

theorem roots_filter (F : Clusters L) {p : Finset L → Prop} [DecidablePred p] (h : ∀ A B, A ⊆ B → p A → p B) :
    roots (F.filter p) = (roots F).filter p := by ext; grind [mem_roots]

private theorem roots_insert {F : Clusters L} {U : Finset L} (h : ∀ C ∈ F, ¬ U ⊆ C) :
    roots (insert U F) = insert U ((roots F).filter fun C => ¬C ⊆ U) := by grind [mem_roots]

/-- Joining two roots preserves the forest and replaces just those roots by their union. -/
private theorem update {F P : Clusters L} (hf : IsForest F) (hp : P ∈ (roots F).powersetCard 2) :
    lineages P ∉ F ∧ IsForest (joined F P) ∧ roots (joined F P) = insert (lineages P) (roots F \ P) ∧ lineages (joined F P) = lineages F := by
  obtain ⟨A,ha,B,hb,ne,rfl⟩ := mem_pairs.mp hp
  have fresh (C) (hc : C ∈ F) : ¬ A ∪ B ⊆ C := by grind [mem_roots]
  have ok (C) (hc : C ∈ F) : Compatible C (A ∪ B) := by
    obtain ⟨R,hr,le⟩ := exists_mem_roots_subset hc
    have := hf.disjoint_of_mem_roots hr ha; have := hf.disjoint_of_mem_roots hr hb
    grind [Finset.disjoint_left]
  have nA := hf.1 A (roots_subset _ ha)
  rw [joined_pair,show lineages {A,B} = A ∪ B by simp [lineages],lineages_insert]
  refine ⟨fun h => fresh _ h subset_rfl,?_,?_,?_⟩
  · grind [IsForest,Compatible.flip,Finset.Nonempty]
  · rw [roots_insert fresh]; congr 1; ext R
    simp only [mem_filter,mem_sdiff,and_congr_right_iff]; intro hr
    have := hf.disjoint_of_mem_roots hr ha; have := hf.disjoint_of_mem_roots hr hb
    have := hf.1 R (roots_subset _ hr); grind [Finset.disjoint_left,Finset.Nonempty]
  · have := subset_lineages (roots_subset _ ha); have := subset_lineages (roots_subset _ hb)
    change _ ∪ lineages F = _; grind

private theorem lost_roots {F P : Clusters L} (hf : IsForest F) (hp : P ∈ (roots F).powersetCard 2) :
    roots F \ roots (joined F P) = P := by
  obtain ⟨hs,hk⟩ := mem_powersetCard.mp hp
  obtain ⟨hn,_,e,_⟩ := update hf hp; rw [e]; grind [mem_roots]

theorem joined_inj {F : Clusters L} (hF : IsForest F) : Set.InjOn (joined F) ↑((roots F).powersetCard 2) :=
  fun P hp Q hq e => by rw [← lost_roots hF hp,← lost_roots hF hq,e]

theorem IsForest.card_merges {F : Clusters L} (hF : IsForest F) : #(merges F) = (#(roots F)).choose 2 := by
  rw [merges,card_image_of_injOn (joined_inj hF),card_powersetCard]

/-- What a merge of a forest is. -/
theorem IsForest.of_mem_merges {F G : Clusters L} (hF : IsForest F) (hG : G ∈ merges F) :
    IsForest G ∧ #(roots G) + 1 = #(roots F) ∧ F ⊂ G ∧ lineages G = lineages F := by
  obtain ⟨P,hp,rfl⟩ := mem_image.mp hG; obtain ⟨hs,hk⟩ := mem_powersetCard.mp hp
  obtain ⟨hn,hf,e,hl⟩ := update hF hp
  refine ⟨hf,?_,ssubset_insert hn,hl⟩
  rw [e,card_insert_of_notMem (by grind [mem_roots]),card_sdiff_of_subset hs]
  have := card_le_card hs; omega

/-! ### More on merges and the generator -/

/-- A forest with at most one root has no merges. -/
theorem merges_eq_empty_of_card_roots_le_one {F : Clusters L} (h : #(roots F) ≤ 1) :
    merges F = ∅ := by
  simp_all [merges]

/-- First-step decomposition at a forest `F` with `k` roots:
`∑ G, Q(F, G) v(G) = -(k choose 2) v(F) + ∑ G ∈ merges F, v(G)`. -/
theorem IsForest.sum_kingmanGenerator_mul {F : Clusters L} (hF : IsForest F)
    (v : Clusters L → ℝ) :
    ∑ G, kingmanGenerator F G * v G =
      -((#(roots F)).choose 2 : ℝ) * v F + ∑ G ∈ merges F, v G := by
  simp only [kingmanGenerator,←mem_merges,ite_mul,one_mul,zero_mul,←sum_erase_add _ _ (mem_univ F),ite_true]
  rw [sum_congr rfl fun G hg => ite_eq_right (ne_of_mem_erase hg)]
  simp [sum_ite_mem,erase_inter,show F ∉ merges F from fun h => (hF.of_mem_merges h).2.2.1.false,add_comm]

theorem IsForest.generator_pairs {F : Clusters L} (hF : IsForest F) (u : Clusters L → ℝ) :
    ∑ G, kingmanGenerator F G * u G = ∑ P ∈ (roots F).powersetCard 2, (u (joined F P) - u F) := by
  rw [hF.sum_kingmanGenerator_mul,merges,sum_image (joined_inj hF),sum_sub_distrib,sum_const,card_powersetCard,nsmul_eq_mul]; ring

end ADR11
