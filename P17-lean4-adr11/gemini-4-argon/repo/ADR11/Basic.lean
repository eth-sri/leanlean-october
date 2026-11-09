module

public import ADR11.Defs

@[expose] public section

namespace ADR11

open Finset Real Filter Topology

variable {X : Type*} [Fintype X] [DecidableEq X] {L : Type*} [Fintype L] [DecidableEq L]

def hierarchyOf (C : Finset (Finset X)) : Finset (Finset X) :=
  insert univ (C ∪ univ.image ({·}))

def treeOfClusters (C : Finset (Finset X)) : Finset (Finset X) :=
  unroot (hierarchyOf C)

local notation "sub" S:max A:max => Finset.subtype (· ∈ S) A

def restrictClusters (S : Finset X) (H : Finset (Finset X)) : Finset (Finset S) :=
  (H.filter fun A => (A ∩ S).Nonempty).image fun A => sub S A

theorem mem_restrictClusters {S : Finset X} {H : Finset (Finset X)} {C : Finset S} :
    C ∈ restrictClusters S H ↔ ∃ A ∈ H, (A ∩ S).Nonempty ∧ sub S A = C := by
  simp [restrictClusters, and_assoc]

theorem subtype_mem_restrictClusters {S : Finset X} {H : Finset (Finset X)} {A : Finset X}
    (hA : A ∈ H) (hAS : (A ∩ S).Nonempty) : sub S A ∈ restrictClusters S H :=
  mem_restrictClusters.2 ⟨A, hA, hAS, rfl⟩

theorem subtype_nonempty_iff {S A : Finset X} :
    (sub S A).Nonempty ↔ (A ∩ S).Nonempty :=
  ⟨fun ⟨x, hx⟩ => ⟨x, mem_inter.2 ⟨mem_subtype.1 hx, x.2⟩⟩,
    fun ⟨x, hx⟩ => ⟨⟨x, (mem_inter.1 hx).2⟩, mem_subtype.2 (mem_inter.1 hx).1⟩⟩

theorem subtype_compl {S : Finset X} (A : Finset X) :
    sub S Aᶜ = (sub S A)ᶜ := by
  ext x; simp [mem_subtype, mem_compl]

theorem subtype_ne_univ_iff {S A : Finset X} :
    sub S A ≠ univ ↔ (Aᶜ ∩ S).Nonempty := by
  rw [← subtype_nonempty_iff, subtype_compl, Ne, ← compl_eq_empty_iff,
    ← not_nonempty_iff_eq_empty, not_not]

theorem mem_iff_of_subtype_eq {S A B : Finset X}
    (h : sub S A = sub S B) {x : X} (hx : x ∈ S) : x ∈ A ↔ x ∈ B := by
  simpa [mem_subtype] using Finset.ext_iff.1 h ⟨x, hx⟩

theorem mem_unroot {G : Finset (Finset L)} {A : Finset L} :
    A ∈ unroot G ↔ (A ∈ G ∧ A ≠ univ) ∨ (Aᶜ ∈ G ∧ Aᶜ ≠ univ) := by
  simp only [unroot, mem_union, mem_erase, mem_image]
  exact ⟨by rintro (⟨h1, h2⟩ | ⟨B, ⟨h1, h2⟩, rfl⟩); exacts [Or.inl ⟨h2, h1⟩, Or.inr ⟨by simpa using h2, by simpa using h1⟩],
    by rintro (⟨h1, h2⟩ | ⟨h1, h2⟩); exacts [Or.inl ⟨h2, h1⟩, Or.inr ⟨Aᶜ, ⟨h2, h1⟩, compl_compl A⟩]⟩

theorem compl_mem_unroot {G : Finset (Finset L)} {A : Finset L} :
    Aᶜ ∈ unroot G ↔ A ∈ unroot G := by
  rw [mem_unroot, mem_unroot, compl_compl, or_comm]

theorem laminar_of_mem_unroot (σ : SpeciesTree X) {A B : Finset X}
    (hA : A ∈ unroot σ.clusters) (hB : B ∈ unroot σ.clusters) :
    A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ Aᶜ ⊆ B := by
  rcases mem_unroot.1 hA with ⟨hA, -⟩ | ⟨hA, -⟩ <;>
    rcases mem_unroot.1 hB with ⟨hB, -⟩ | ⟨hB, -⟩ <;>
    have h := σ.laminar _ hA _ hB
  · tauto
  · rw [subset_compl_iff_disjoint_right, ← compl_subset_compl, compl_compl,
      disjoint_compl_right_iff] at h; tauto
  · rw [subset_compl_iff_disjoint_right, disjoint_comm, disjoint_compl_left_iff] at h; tauto
  · rw [compl_subset_compl, compl_subset_compl, disjoint_compl_right_iff] at h; tauto

namespace SpeciesTree

noncomputable def restrictLength (σ : SpeciesTree X) (S : Finset X) (C : Finset S) : ℝ :=
  ∑ A ∈ σ.clusters with A ≠ univ ∧ sub S A = C, σ.length A

noncomputable def restrict (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    SpeciesTree S where
  clusters := restrictClusters S σ.clusters
  univ_mem := subtype_univ (· ∈ S) ▸ subtype_mem_restrictClusters σ.univ_mem (by simpa using hS)
  singleton_mem x := mem_restrictClusters.2
    ⟨{x.1}, σ.singleton_mem x.1, ⟨x.1, by simp [x.2]⟩, by ext ⟨y, hy⟩; simp [Subtype.ext_iff]⟩
  nonempty_of_mem C hC := by
    obtain ⟨A, -, hAS, rfl⟩ := mem_restrictClusters.1 hC
    exact subtype_nonempty_iff.2 hAS
  laminar C hC D hD := by
    obtain ⟨A, hA, -, rfl⟩ := mem_restrictClusters.1 hC
    obtain ⟨B, hB, -, rfl⟩ := mem_restrictClusters.1 hD
    rcases σ.laminar A hA B hB with h | h | h
    · exact Or.inl (subtype_mono h)
    · exact Or.inr (Or.inl (subtype_mono h))
    · exact Or.inr (Or.inr (disjoint_left.2 fun a ha hb =>
        disjoint_left.1 h (mem_subtype.1 ha) (mem_subtype.1 hb)))
  length := σ.restrictLength S
  length_pos C hC hCu := by
    obtain ⟨A, hA, -, rfl⟩ := mem_restrictClusters.1 hC
    exact sum_pos (fun B hB => σ.length_pos B (mem_filter.1 hB).1 (mem_filter.1 hB).2.1)
      ⟨A, mem_filter.2 ⟨hA, fun e => hCu (e ▸ subtype_univ _), rfl⟩⟩

@[simp] theorem restrict_clusters (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    (σ.restrict S hS).clusters = restrictClusters S σ.clusters := rfl

@[simp] theorem restrict_length (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    (σ.restrict S hS).length = σ.restrictLength S := rfl

theorem restrictLength_subtype_eq (σ : SpeciesTree X) {S A : Finset X} (hA : A ∈ σ.clusters)
    (hAu : A ≠ univ)
    (h : ∀ B ∈ σ.clusters, sub S B = sub S A → B = A) :
    σ.restrictLength S (sub S A) = σ.length A :=
  Finset.sum_eq_single_of_mem A (mem_filter.2 ⟨hA, hAu, rfl⟩) fun B hB hBA =>
    absurd (h B (mem_filter.1 hB).1 (mem_filter.1 hB).2.2) hBA

theorem mem_unroot_restrict (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) {C : Finset S} :
    C ∈ unroot (σ.restrict S hS).clusters ↔
      ∃ A ∈ unroot σ.clusters, (A ∩ S).Nonempty ∧ (Aᶜ ∩ S).Nonempty ∧ sub S A = C := by
  rw [mem_unroot, restrict_clusters]
  constructor
  · rintro (⟨hC, hCu⟩ | ⟨hC, hCu⟩)
    · obtain ⟨A, hA, hAS, rfl⟩ := mem_restrictClusters.1 hC
      exact ⟨A, mem_unroot.2 (Or.inl ⟨hA, fun e => hCu (e ▸ subtype_univ _)⟩),
        hAS, subtype_ne_univ_iff.1 hCu, rfl⟩
    · obtain ⟨A, hA, hAS, hAC⟩ := mem_restrictClusters.1 hC
      exact ⟨Aᶜ, compl_mem_unroot.2 (mem_unroot.2
        (Or.inl ⟨hA, fun e => hCu (hAC ▸ e ▸ subtype_univ _)⟩)),
        subtype_ne_univ_iff.1 (hAC ▸ hCu), by rwa [compl_compl],
        by rw [subtype_compl, hAC, compl_compl]⟩
  · rintro ⟨A, hA, hAS, hAcS, rfl⟩
    rcases mem_unroot.1 hA with ⟨hA', -⟩ | ⟨hA', -⟩
    · exact Or.inl ⟨subtype_mem_restrictClusters hA' hAS, subtype_ne_univ_iff.2 hAcS⟩
    · rw [← subtype_compl]
      exact Or.inr ⟨subtype_mem_restrictClusters hA' hAcS,
        subtype_ne_univ_iff.2 (by rwa [compl_compl])⟩

theorem restrict_unrootedLength (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty)
    (C : Finset S) (hC₁ : 2 ≤ #C) (hC₂ : 2 ≤ #Cᶜ) :
    (σ.restrict S hS).unrootedLength C =
      ∑ A ∈ σ.clusters with A ≠ univ ∧ (sub S A = C ∨ sub S A = Cᶜ),
        σ.length A := by
  have hCne : C.Nonempty := card_pos.1 (by omega)
  have hCcne : Cᶜ.Nonempty := card_pos.1 (by omega)
  have hCu : C ≠ univ := by rw [← compl_compl C]; exact (compl_ne_univ_iff_nonempty Cᶜ).2 hCcne
  have hCcu : Cᶜ ≠ univ := (compl_ne_univ_iff_nonempty C).2 hCne
  unfold unrootedLength
  rw [restrict_clusters, restrict_length]
  unfold restrictLength
  symm
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun A => sub S A)
    (t := (restrictClusters S σ.clusters).filter (fun D => D ≠ univ ∧ (D = C ∨ D = Cᶜ)))]
  · refine Finset.sum_congr rfl fun D hD => ?_
    rw [filter_filter]
    exact Finset.sum_congr (filter_congr fun A _ =>
      ⟨fun ⟨⟨h2, _⟩, h3⟩ => ⟨h2, h3⟩, fun ⟨h2, h3⟩ => ⟨⟨h2, h3 ▸ (mem_filter.1 hD).2.2⟩, h3⟩⟩)
      fun _ _ => rfl
  · intro A hA
    obtain ⟨hA1, -, hA3⟩ := mem_filter.1 hA
    refine mem_filter.2 ⟨mem_restrictClusters.2 ⟨A, hA1, subtype_nonempty_iff.1 ?_, rfl⟩, ?_, hA3⟩
    · rcases hA3 with h | h <;> rw [h] <;> assumption
    · rcases hA3 with h | h <;> rw [h] <;> assumption

theorem unrootedLength_compl (σ : SpeciesTree X) (A : Finset X) :
    σ.unrootedLength Aᶜ = σ.unrootedLength A := by
  unfold unrootedLength
  refine Finset.sum_congr (filter_congr fun B _ => ?_) fun _ _ => rfl
  rw [compl_compl, or_comm]

end SpeciesTree

def IsForest (F : Finset (Finset L)) : Prop :=
  (∀ A ∈ F, A.Nonempty) ∧ ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

def merges (F : Finset (Finset L)) : Finset (Finset (Finset L)) :=
  ((roots F ×ˢ roots F).filter fun p => p.1 ≠ p.2).image fun p => insert (p.1 ∪ p.2) F

def lineages (F : Finset (Finset L)) : Finset L :=
  F.sup id

theorem mem_roots {F : Finset (Finset L)} {A : Finset L} :
    A ∈ roots F ↔ A ∈ F ∧ ∀ B ∈ F, A ⊆ B → B = A := mem_filter

theorem roots_subset (F : Finset (Finset L)) : roots F ⊆ F := filter_subset _ _

theorem mem_merges {F G : Finset (Finset L)} :
    G ∈ merges F ↔ ∃ A ∈ roots F, ∃ B ∈ roots F, A ≠ B ∧ G = insert (A ∪ B) F := by
  unfold merges
  simp only [mem_image, mem_filter, mem_product, Prod.exists]
  exact ⟨fun ⟨A, B, ⟨⟨hA, hB⟩, hAB⟩, h⟩ => ⟨A, hA, B, hB, hAB, h.symm⟩,
    fun ⟨A, hA, B, hB, hAB, h⟩ => ⟨A, B, ⟨⟨hA, hB⟩, hAB⟩, h.symm⟩⟩

theorem mem_lineages {F : Finset (Finset L)} {l : L} : l ∈ lineages F ↔ ∃ A ∈ F, l ∈ A := by
  simp [lineages]

theorem subset_lineages {F : Finset (Finset L)} {A : Finset L} (hA : A ∈ F) : A ⊆ lineages F :=
  le_sup (f := id) hA

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

theorem lineages_roots {F : Finset (Finset L)} : lineages (roots F) = lineages F :=
  (sup_mono (roots_subset F)).antisymm <| Finset.sup_le fun _ hA =>
    let ⟨_, hR, hAR⟩ := exists_mem_roots_subset hA; hAR.trans (subset_lineages hR)

private theorem forest_not_union_subset {F : Finset (Finset L)} {A B D : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hAB : A ≠ B) (hD : D ∈ F) : ¬ A ∪ B ⊆ D := fun h =>
  hAB (((mem_roots.1 hA).2 D hD (subset_union_left.trans h)).symm.trans
    ((mem_roots.1 hB).2 D hD (subset_union_right.trans h)))

theorem union_not_mem_of_mem_roots {F : Finset (Finset L)} {A B : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hAB : A ≠ B) : A ∪ B ∉ F :=
  fun h => forest_not_union_subset hA hB hAB h subset_rfl

private theorem forest_root_subset_union {F : Finset (Finset L)} (hF : IsForest F)
    {A B C : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) (hC : C ∈ roots F)
    (h : C ⊆ A ∪ B) : C = A ∨ C = B := by
  by_contra! hne
  obtain ⟨x, hx⟩ := hF.1 C (roots_subset F hC)
  exact (mem_union.1 (h hx)).elim
    (disjoint_left.1 (hF.disjoint_of_mem_roots hC hA hne.1) hx)
    (disjoint_left.1 (hF.disjoint_of_mem_roots hC hB hne.2) hx)

private theorem forest_subset_or_disjoint_union {F : Finset (Finset L)} (hF : IsForest F)
    {A B C : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) (hC : C ∈ F) :
    C ⊆ A ∪ B ∨ Disjoint C (A ∪ B) := by
  obtain ⟨R, hR, hCR⟩ := exists_mem_roots_subset hC
  by_cases hRA : R = A
  · exact Or.inl (hCR.trans (hRA ▸ subset_union_left))
  by_cases hRB : R = B
  · exact Or.inl (hCR.trans (hRB ▸ subset_union_right))
  exact Or.inr (disjoint_union_right.2
    ⟨(hF.disjoint_of_mem_roots hR hA hRA).mono_left hCR,
     (hF.disjoint_of_mem_roots hR hB hRB).mono_left hCR⟩)

theorem IsForest.isForest_merge {F : Finset (Finset L)} (hF : IsForest F) {A B : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) : IsForest (insert (A ∪ B) F) := by
  refine ⟨fun C hC => (mem_insert.1 hC).elim
      (fun h => h ▸ (hF.1 A (roots_subset F hA)).mono subset_union_left) (hF.1 C),
    fun C hC D hD => ?_⟩
  rcases mem_insert.1 hC with rfl | hC <;> rcases mem_insert.1 hD with rfl | hD
  · exact Or.inl subset_rfl
  · exact (forest_subset_or_disjoint_union hF hA hB hD).elim (Or.inr ∘ Or.inl)
      (fun h => Or.inr (Or.inr h.symm))
  · exact (forest_subset_or_disjoint_union hF hA hB hC).elim Or.inl (Or.inr ∘ Or.inr)
  · exact hF.2 C hC D hD

theorem IsForest.merge_inj {F : Finset (Finset L)} (hF : IsForest F)
    {A B C D : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) (hAB : A ≠ B)
    (hC : C ∈ roots F) (hD : D ∈ roots F) (hCD : C ≠ D)
    (hzw : insert (A ∪ B) F = insert (C ∪ D) F) : s(A, B) = s(C, D) := by
  have hU : A ∪ B = C ∪ D :=
    (mem_insert.1 (hzw ▸ mem_insert_self _ _)).resolve_right (union_not_mem_of_mem_roots hA hB hAB)
  rcases forest_root_subset_union hF hA hB hC (hU ▸ subset_union_left) with rfl | rfl <;>
    rcases forest_root_subset_union hF hA hB hD (hU ▸ subset_union_right) with rfl | rfl
  · exact absurd rfl hCD
  · rfl
  · exact Sym2.eq_swap
  · exact absurd rfl hCD

theorem IsForest.card_merges {F : Finset (Finset L)} (hF : IsForest F) :
    #(merges F) = (#(roots F)).choose 2 := by
  let g : Sym2 (Finset L) → Finset (Finset L) :=
    Sym2.lift ⟨fun A B => insert (A ∪ B) F, fun A B => by simp only [union_comm]⟩
  have hg : ∀ A B, g s(A, B) = insert (A ∪ B) F := Sym2.lift_mk _
  have h1 : merges F = ((roots F).offDiag.image Sym2.mk.uncurry).image g := by
    ext G; rw [mem_merges, image_image, mem_image]
    exact ⟨fun ⟨A, hA, B, hB, hAB, h⟩ => ⟨(A, B), mem_offDiag.2 ⟨hA, hB, hAB⟩, h ▸ hg A B⟩,
      fun ⟨⟨A, B⟩, hp, h⟩ => let ⟨hA, hB, hAB⟩ := mem_offDiag.1 hp
        ⟨A, hA, B, hB, hAB, h ▸ (hg A B).symm⟩⟩
  rw [h1, card_image_of_injOn, Sym2.card_image_offDiag]
  rintro _ hz _ hw hzw
  obtain ⟨⟨A, B⟩, hp, rfl⟩ := mem_image.1 hz
  obtain ⟨⟨C, D⟩, hq, rfl⟩ := mem_image.1 hw
  obtain ⟨hA, hB, hAB⟩ : A ∈ _ ∧ B ∈ _ ∧ A ≠ B := mem_offDiag.1 hp
  obtain ⟨hC, hD, hCD⟩ : C ∈ _ ∧ D ∈ _ ∧ C ≠ D := mem_offDiag.1 hq
  exact hF.merge_inj hA hB hAB hC hD hCD ((hg A B).symm.trans (hzw.trans (hg C D)))

theorem IsForest.of_mem_merges {F G : Finset (Finset L)} (hF : IsForest F) (hG : G ∈ merges F) :
    IsForest G ∧ #(roots G) + 1 = #(roots F) ∧ F ⊆ G ∧ G ≠ F ∧ lineages G = lineages F := by
  obtain ⟨A, hA, B, hB, hAB, rfl⟩ := mem_merges.1 hG
  have hrm : roots (insert (A ∪ B) F) = insert (A ∪ B) (((roots F).erase A).erase B) := by
    ext C
    simp only [mem_roots, mem_insert, mem_erase, forall_eq_or_imp]
    constructor
    · rintro (⟨rfl | hC, h1, h2⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨by rintro rfl; exact forest_not_union_subset hA hB hAB hC (h1 subset_union_right).subset,
          by rintro rfl; exact forest_not_union_subset hA hB hAB hC (h1 subset_union_left).subset, hC, h2⟩
    · rintro (rfl | ⟨hCB, hCA, hC, h2⟩)
      · exact ⟨Or.inl rfl, fun _ => rfl, fun D hD h => absurd h (forest_not_union_subset hA hB hAB hD)⟩
      · exact ⟨Or.inr hC, fun h => (forest_root_subset_union hF hA hB (mem_roots.2 ⟨hC, h2⟩) h).elim
          (fun e => absurd e hCA) (fun e => absurd e hCB), h2⟩
  have hU : A ∪ B ∉ ((roots F).erase A).erase B := fun h =>
    union_not_mem_of_mem_roots hA hB hAB (roots_subset F (mem_of_mem_erase (mem_of_mem_erase h)))
  refine ⟨hF.isForest_merge hA hB, ?_, subset_insert _ _,
    fun h => union_not_mem_of_mem_roots hA hB hAB (h ▸ mem_insert_self _ _), ?_⟩
  · rw [hrm, card_insert_of_notMem hU, card_erase_add_one (mem_erase.2 ⟨hAB.symm, hB⟩),
      card_erase_add_one hA]
  · exact sup_insert.trans (sup_eq_right.2 (union_subset
      (subset_lineages (roots_subset F hA)) (subset_lineages (roots_subset F hB))))

theorem kingmanGenerator_apply_of_isForest {F : Finset (Finset L)} (G : Finset (Finset L)) :
    kingmanGenerator F G =
      if G = F then -((#(roots F)).choose 2 : ℝ) else if G ∈ merges F then 1 else 0 := by
  simp only [kingmanGenerator, mem_merges]

theorem IsForest.eq_of_mem_roots_of_mem {F : Finset (Finset L)} (hF : IsForest F)
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) {l : L} (hlA : l ∈ A) (hlB : l ∈ B) :
    A = B := by
  by_contra hAB
  exact disjoint_left.1 (hF.disjoint_of_mem_roots hA hB hAB) hlA hlB

theorem merges_eq_empty_of_card_roots_le_one {F : Finset (Finset L)} (h : #(roots F) ≤ 1) :
    merges F = ∅ :=
  eq_empty_of_forall_notMem fun _ hG =>
    let ⟨A, hA, B, hB, hAB, _⟩ := mem_merges.1 hG; hAB (card_le_one.1 h A hA B hB)

theorem IsForest.sum_kingmanGenerator_mul {F : Finset (Finset L)} (hF : IsForest F)
    (v : Finset (Finset L) → ℝ) :
    ∑ G, kingmanGenerator F G * v G =
      -((#(roots F)).choose 2 : ℝ) * v F + ∑ G ∈ merges F, v G := by
  have hadd (G) : kingmanGenerator F G =
      (if G = F then -((#(roots F)).choose 2 : ℝ) else 0) + (if G ∈ merges F then 1 else 0) := by
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
  rw [Matrix.mul_apply, hF.sum_kingmanGenerator_mul]

theorem isForest_sampledForest (s : L → X) (A : Finset X) :
    IsForest (sampledForest s A) := by
  refine ⟨fun B hB => ?_, fun B hB C hC => ?_⟩
  · obtain ⟨l, -, rfl⟩ := mem_image.1 hB; exact singleton_nonempty l
  · obtain ⟨l, -, rfl⟩ := mem_image.1 hB
    obtain ⟨m, -, rfl⟩ := mem_image.1 hC
    exact (eq_or_ne l m).elim (fun h => Or.inl (h ▸ subset_rfl))
      (fun h => Or.inr (Or.inr (disjoint_singleton.2 h)))


/-- The jump chain of Kingman's coalescent on forests: from a forest with `k ≥ 2` roots, each of
its `k.choose 2` merges has probability `1 / (k choose 2)`; a forest with at most one root stays
put. -/
noncomputable def jumpMatrix : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  fun F G =>
    if #(roots F) ≤ 1 then (if G = F then 1 else 0)
    else if G ∈ merges F then (((#(roots F)).choose 2 : ℕ) : ℝ)⁻¹ else 0

/-- `deathPow m k j` is the entry `(k, j)` of `D^m`, where `D` is the generator of the pure death
process on `ℕ` with rate `k.choose 2` from `k` to `k - 1`. -/
def deathPow : ℕ → ℕ → ℕ → ℝ
  | 0, k, j => if k = j then 1 else 0
  | m + 1, k, j => ((k.choose 2 : ℕ) : ℝ) * (deathPow m (k - 1) j - deathPow m k j)

/-- The transition probabilities `exp(tD)(k, j)` of the pure death process: the probability that
`k` lineages coalesce into `j` lineages within time `t`. -/
noncomputable def deathProb (k j : ℕ) (t : ℝ) : ℝ :=
  ∑' m : ℕ, t ^ m / (m.factorial : ℝ) * deathPow m k j

theorem jumpMatrix_apply_of_isForest {F : Finset (Finset L)}
    (hk : 2 ≤ #(roots F)) (G : Finset (Finset L)) :
    jumpMatrix F G = if G ∈ merges F then (((#(roots F)).choose 2 : ℕ) : ℝ)⁻¹ else 0 := by
  simp only [jumpMatrix, ite_eq_right (by omega : ¬ #(roots F) ≤ 1)]

private theorem fact_jumpMatrix_apply_of_le_one {F : Finset (Finset L)} (hk : #(roots F) ≤ 1)
    (G : Finset (Finset L)) : jumpMatrix F G = if G = F then 1 else 0 := by
  simp only [jumpMatrix, ite_eq_left hk]

private theorem fact_one_apply (F G : Finset (Finset L)) :
    (1 : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ) F G = if G = F then 1 else 0 := by
  simp [Matrix.one_apply, eq_comm]

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
    · subst hGF; exact ⟨hF, subset_rfl, rfl, by split_ifs <;> omega⟩
    · exact absurd rfl h
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply] at h
    obtain ⟨F', -, hF'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hJ : jumpMatrix F F' ≠ 0 := left_ne_zero_of_mul hF'
    have hJn : (jumpMatrix ^ n) F' G ≠ 0 := right_ne_zero_of_mul hF'
    by_cases hk : #(roots F) ≤ 1
    · obtain rfl : F' = F := by_contra fun hne =>
        hJ (by rw [fact_jumpMatrix_apply_of_le_one hk, ite_eq_right hne])
      obtain ⟨h1, h2, h3, h4⟩ := ih hF hJn
      exact ⟨h1, h2, h3, by rw [h4]; split_ifs <;> omega⟩
    · replace hk : 2 ≤ #(roots F) := by omega
      have hmem : F' ∈ merges F := by_contra fun hne =>
        hJ (by rw [jumpMatrix_apply_of_isForest hk, ite_eq_right hne])
      obtain ⟨hF'f, hcard, hsub, -, hlin⟩ := hF.of_mem_merges hmem
      obtain ⟨h1, h2, h3, h4⟩ := ih hF'f hJn
      exact ⟨h1, hsub.trans h2, h3.trans hlin, by rw [h4]; split_ifs <;> omega⟩

theorem deathPow_succ (m k j : ℕ) :
    deathPow (m + 1) k j = ((k.choose 2 : ℕ) : ℝ) * (deathPow m (k - 1) j - deathPow m k j) :=
  rfl

theorem deathPow_eq_zero_of_lt {k j : ℕ} (h : k < j) (m : ℕ) : deathPow m k j = 0 := by
  induction m generalizing k with
  | zero => simp [deathPow, h.ne]
  | succ m ih => rw [deathPow_succ, ih (lt_of_le_of_lt (Nat.sub_le k 1) h), ih h]; ring

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
  rw [Real.exp_eq_exp_ℝ]
  convert NormedSpace.expSeries_div_hasSum_exp (x * t) using 1
  funext m; rw [mul_pow]; ring

private theorem deathProb_self (k : ℕ) (t : ℝ) :
    deathProb k k t = exp (-(((k.choose 2 : ℕ) : ℝ) * t)) := by
  simpa only [deathProb, deathPow_self, neg_mul] using
    (fact_hasSum_exp_mul (-((k.choose 2 : ℕ) : ℝ)) t).tsum_eq

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
    · rw [Nat.choose_eq_zero_of_lt (by omega : #(roots F) < 2),
        merges_eq_empty_of_card_roots_le_one hk]; simp
    · replace hk : 2 ≤ #(roots F) := by omega
      by_cases hjk : #(roots G) < #(roots F)
      · have hstep := jumpMatrix_pow_succ_apply hk (#(roots F) - 1 - #(roots G)) G
        rw [show #(roots F) - 1 - #(roots G) + 1 = #(roots F) - #(roots G) by omega] at hstep
        have hC : (((#(roots F)).choose 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
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
      Nat.choose_eq_zero_of_lt (by omega : #(roots G) < 2)]; simp
  · rw [jumpMatrix_pow_of_card_roots_le_one hk, ite_eq_right hG, mul_zero]

theorem kingmanTransition_nonneg {t : ℝ} (ht : 0 ≤ t) (F G : Finset (Finset L)) :
    0 ≤ kingmanTransition t F G := by
  set Q := kingmanGenerator (L := L) with hQ
  set c : ℝ := ∑ F : Finset (Finset L), (((#(roots F)).choose 2 : ℕ) : ℝ)
  set P : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ := Q + c • 1 with hPdef
  have hP (F G) : 0 ≤ P F G := by
    rw [hPdef, Matrix.add_apply, Matrix.smul_apply, fact_one_apply, smul_eq_mul, hQ]
    unfold kingmanGenerator
    by_cases h : G = F
    · subst h; simp only [ite_true, mul_one]
      have : (((#(roots G)).choose 2 : ℕ) : ℝ) ≤ c :=
        Finset.single_le_sum (f := fun F : Finset (Finset L) => (((#(roots F)).choose 2 : ℕ) : ℝ))
          (fun _ _ => by positivity) (Finset.mem_univ G)
      linarith
    · simp only [ite_eq_right h, mul_zero, add_zero]; split_ifs <;> norm_num
  have hPn (n) : ∀ F G, 0 ≤ (P ^ n) F G := by
    induction n with
    | zero => intro F G; rw [pow_zero, fact_one_apply]; split_ifs <;> norm_num
    | succ n ih =>
      intro F G; rw [pow_succ', Matrix.mul_apply]
      exact Finset.sum_nonneg fun F' _ => mul_nonneg (hP F F') (ih F' G)
  have hexpP (F G) : 0 ≤ NormedSpace.exp (t • P) F G :=
    (fact_hasSum_exp_apply (t • P) F G).nonneg fun n => by
      rw [smul_pow, Matrix.smul_apply, smul_eq_mul]
      exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg ht n) (hPn n F G))
  have hscal (r : ℝ) (F G) : 0 ≤
      NormedSpace.exp (r • (1 : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ)) F G := by
    have h := fact_hasSum_exp_apply
      (r • (1 : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ)) F G
    simp_rw [smul_pow, one_pow, Matrix.smul_apply, fact_one_apply, smul_eq_mul] at h
    by_cases hGF : G = F
    · simp only [ite_eq_left hGF, mul_one, ← div_eq_inv_mul] at h
      rw [h.unique (by simpa using fact_hasSum_exp_mul 1 r)]; positivity
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


private theorem absorb_deathPow_zero (m k : ℕ) (hk : 1 ≤ k) : deathPow m k 0 = 0 := by
  induction m generalizing k with
  | zero => simp [deathPow, show k ≠ 0 by omega]
  | succ m ih =>
    simp only [deathPow]
    rcases Nat.lt_or_ge k 2 with h | h
    · obtain rfl : k = 1 := by omega
      simp
    · rw [ih (k - 1) (by omega), ih k hk, sub_self, mul_zero]

private theorem absorb_exists_deathPow (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    ∃ c : ℕ → ℝ, c 1 = 1 ∧ ∀ m,
      deathPow m k j = ∑ r ∈ Icc j k, c r * (-((r.choose 2 : ℕ) : ℝ)) ^ m := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases eq_or_lt_of_le hjk with rfl | hlt
    · exact ⟨fun _ => 1, rfl, fun m => by simp [deathPow_self]⟩
    · obtain ⟨c', hc'1, hc'⟩ := ih (by omega)
      let f (r : ℕ) : ℝ := (((k + 1).choose 2 : ℕ) : ℝ) /
        ((((k + 1).choose 2 : ℕ) : ℝ) - ((r.choose 2 : ℕ) : ℝ)) * c' r
      let c (r : ℕ) : ℝ := if r = k + 1 then -∑ s ∈ Icc j k, f s else f r
      have hK0 : (0 : ℝ) < (((k + 1).choose 2 : ℕ) : ℝ) := by
        exact_mod_cast Nat.choose_pos (by omega : 2 ≤ k + 1)
      have hc1 : c 1 = 1 := by
        simp only [c, ite_eq_right (by omega : (1 : ℕ) ≠ k + 1), f,
          show Nat.choose 1 2 = 0 from rfl, Nat.cast_zero, sub_zero, div_self hK0.ne', hc'1, mul_one]
      have hcr : ∀ r ∈ Icc j k,
          ((((k + 1).choose 2 : ℕ) : ℝ) - ((r.choose 2 : ℕ) : ℝ)) * c r =
            (((k + 1).choose 2 : ℕ) : ℝ) * c' r := fun r hr => by
        have hlt' : r.choose 2 < (k + 1).choose 2 := by
          have := Nat.choose_le_choose 2 (mem_Icc.1 hr).2
          rw [show (k + 1).choose 2 = k.choose 1 + k.choose 2 from rfl, Nat.choose_one_right]; omega
        simp only [c, ite_eq_right (by have := (mem_Icc.1 hr).2; omega : r ≠ k + 1), f]
        rw [← mul_assoc, mul_div_cancel₀ _ (sub_ne_zero.2 (by exact_mod_cast hlt'.ne'))]
      refine ⟨c, hc1, fun m => ?_⟩
      induction m with
      | zero =>
        simp only [deathPow, ite_eq_right hlt.ne', pow_zero, mul_one]
        rw [sum_Icc_succ_top hjk, sum_congr rfl fun r hr =>
          ite_eq_right (by have := (mem_Icc.1 hr).2; omega : r ≠ k + 1)]
        simp [c]
      | succ m ihm =>
        rw [deathPow_succ, Nat.add_sub_cancel, hc' m, ihm, sum_Icc_succ_top hjk,
          sum_Icc_succ_top hjk, mul_sub, mul_add, mul_sum, mul_sum, sub_add_eq_sub_sub,
          ← sum_sub_distrib, sub_eq_add_neg]
        congr 1
        · refine sum_congr rfl fun r hr => ?_
          have := hcr r hr
          rw [pow_succ]; linear_combination -((-((r.choose 2 : ℕ) : ℝ)) ^ m) * this
        · rw [pow_succ]; ring

private theorem absorb_tendsto_exp (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun t : ℝ => exp (-(((m.choose 2 : ℕ) : ℝ) * t))) atTop
      (𝓝 (if m = 1 then 1 else 0)) := by
  split_ifs with h
  · subst h; simp
  · exact tendsto_exp_comp_nhds_zero.mpr (tendsto_neg_atTop_atBot.comp
      (Tendsto.const_mul_atTop (by exact_mod_cast Nat.choose_pos (by omega)) tendsto_id))

theorem tendsto_deathProb (k j : ℕ) (hk : 1 ≤ k) :
    Tendsto (deathProb k j) atTop (𝓝 (if j = 1 then 1 else 0)) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [show deathProb k 0 = fun _ => 0 from funext fun _ => by simp [deathProb, absorb_deathPow_zero _ _ hk],
      ite_eq_right (by norm_num)]
    exact tendsto_const_nhds
  rcases lt_or_ge k j with hkj | hjk
  · rw [show deathProb k j = fun _ => 0 from funext (deathProb_eq_zero_of_lt hkj),
      ite_eq_right (by omega)]
    exact tendsto_const_nhds
  obtain ⟨c, hc1, hc⟩ := absorb_exists_deathPow k j hj hjk
  have h : deathProb k j = fun t => ∑ m ∈ Icc j k, c m * exp (-(((m.choose 2 : ℕ) : ℝ) * t)) := by
    funext t
    have key : ∀ r ∈ Icc j k, HasSum (fun m : ℕ => t ^ m / (m.factorial : ℝ) *
        (c r * (-(((r.choose 2 : ℕ) : ℝ))) ^ m))
        (c r * exp (-(((r.choose 2 : ℕ) : ℝ) * t))) := fun r _ => by
      rw [← neg_mul]
      convert (fact_hasSum_exp_mul (-((r.choose 2 : ℕ) : ℝ)) t).mul_left (c r) using 1
      funext m; ring
    unfold deathProb
    rw [← (hasSum_sum key).tsum_eq]
    exact tsum_congr fun m => by rw [hc m, mul_sum]
  have hlim : (if j = 1 then (1 : ℝ) else 0) =
      ∑ m ∈ Icc j k, c m * (if m = 1 then (1 : ℝ) else 0) := by
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq' (Icc j k) 1 c, mem_Icc]
    split_ifs <;> first | omega | rfl | exact hc1.symm
  rw [h, hlim]
  exact tendsto_finsetSum _ fun m hm =>
    (absorb_tendsto_exp m (by have := (Finset.mem_Icc.1 hm).1; omega)).const_mul _

private theorem absorb_tendsto {F : Finset (Finset L)} (hF : IsForest F)
    (G : Finset (Finset L)) :
    Tendsto (fun t => kingmanTransition t F G) atTop
      (𝓝 ((jumpMatrix ^ (#(roots F) - 1)) F G)) := by
  rcases Nat.eq_zero_or_pos (#(roots F)) with h0 | hpos
  · simp [kingmanTransition_of_card_roots_le_one hF (by omega),
      jumpMatrix_pow_of_card_roots_le_one (by omega : #(roots F) ≤ 1)]
  · simp_rw [kingmanTransition_apply hF]
    have hl := (tendsto_deathProb (#(roots F)) (#(roots G)) hpos).mul_const
      ((jumpMatrix ^ (#(roots F) - #(roots G))) F G)
    by_cases hG : #(roots G) = 1
    · simpa [hG] using hl
    · have h0 : (jumpMatrix ^ (#(roots F) - 1)) F G = 0 := by_contra fun h => hG <| by
        have := (jumpMatrix_pow_support hF h).2.2.2; split_ifs at this <;> omega
      simpa [hG, h0] using hl

theorem kingmanAbsorption_apply {F : Finset (Finset L)} (hF : IsForest F)
    (G : Finset (Finset L)) :
    kingmanAbsorption F G = (jumpMatrix ^ (#(roots F) - 1)) F G :=
  (absorb_tendsto hF G).limUnder_eq

theorem tendsto_kingmanTransition {F : Finset (Finset L)} (hF : IsForest F)
    (G : Finset (Finset L)) :
    Tendsto (fun t => kingmanTransition t F G) atTop (𝓝 (kingmanAbsorption F G)) :=
  kingmanAbsorption_apply hF G ▸ absorb_tendsto hF G

theorem kingmanAbsorption_nonneg {F : Finset (Finset L)} (hF : IsForest F)
    (G : Finset (Finset L)) : 0 ≤ kingmanAbsorption F G :=
  kingmanAbsorption_apply hF G ▸ jumpMatrix_pow_nonneg _ _ _

theorem kingmanAbsorption_sum {F : Finset (Finset L)} (hF : IsForest F) :
    ∑ G, kingmanAbsorption F G = 1 := by
  have h1 : Tendsto (fun t => ∑ G, kingmanTransition t F G) atTop
      (𝓝 (∑ G, kingmanAbsorption F G)) :=
    tendsto_finsetSum _ fun G _ => tendsto_kingmanTransition hF G
  rw [show (fun t => ∑ G, kingmanTransition t F G) = fun _ => 1
    from funext (kingmanTransition_sum hF)] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

theorem kingmanTransition_mul_kingmanAbsorption {F : Finset (Finset L)} (hF : IsForest F)
    (t : ℝ) (G : Finset (Finset L)) :
    ∑ F', kingmanTransition t F F' * kingmanAbsorption F' G = kingmanAbsorption F G := by
  have hlim := (tendsto_kingmanTransition hF G).comp (tendsto_atTop_add_const_left atTop t tendsto_id)
  simp_rw [Function.comp_def, id, kingmanTransition_add, Matrix.mul_apply] at hlim
  refine tendsto_nhds_unique (tendsto_finsetSum _ fun F' _ => ?_) hlim
  by_cases h : kingmanTransition t F F' = 0
  · simp only [h, zero_mul]; exact tendsto_const_nhds
  · rw [kingmanTransition_apply hF] at h
    exact (tendsto_kingmanTransition (jumpMatrix_pow_support hF (right_ne_zero_of_mul h)).1 G).const_mul _

theorem kingmanAbsorption_of_card_roots_le_one {F : Finset (Finset L)} (hF : IsForest F)
    (hk : #(roots F) ≤ 1) (G : Finset (Finset L)) :
    kingmanAbsorption F G = if G = F then 1 else 0 := by
  rw [kingmanAbsorption_apply hF, jumpMatrix_pow_of_card_roots_le_one hk]

/-- A hierarchy of clusters on `X`. -/
def IsHierarchy (H : Finset (Finset X)) : Prop :=
  univ ∈ H ∧ (∀ x : X, {x} ∈ H) ∧ (∀ A ∈ H, A.Nonempty) ∧
    ∀ A ∈ H, ∀ B ∈ H, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

theorem SpeciesTree.isHierarchy (σ : SpeciesTree X) : IsHierarchy σ.clusters :=
  ⟨σ.univ_mem, σ.singleton_mem, σ.nonempty_of_mem, σ.laminar⟩

/-- The distribution of the forest entering the population above `A`: the union of the
independent forests leaving the populations of the children of `A`, together with the singletons
of the lineages sampled at `A`. -/
noncomputable def enteringDist (H : Finset (Finset X)) (len : Finset X → ℝ) (s : L → X)
    (A : Finset X) (F : Finset (Finset L)) : ℝ :=
  ∑ f : childClusters H A → Finset (Finset L),
    if univ.sup f ∪ sampledForest s A = F then ∏ B : childClusters H A, forestDist H len s B (f B)
    else 0

theorem forestDist_eq_sum_entering (H : Finset (Finset X)) (len : Finset X → ℝ) (s : L → X)
    (A : Finset X) (G : Finset (Finset L)) :
    forestDist H len s A G = ∑ F, enteringDist H len s A F * populationKernel len A F G := by
  rw [forestDist]; unfold enteringDist
  simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp_rw [ite_mul, zero_mul]; rw [Finset.sum_ite_eq]; simp

theorem forestDist_of_childClusters_eq_empty {H : Finset (Finset X)} {len : Finset X → ℝ}
    {s : L → X} {A : Finset X} (h : childClusters H A = ∅) (G : Finset (Finset L)) :
    forestDist H len s A G = populationKernel len A (sampledForest s A) G := by
  rw [forestDist]
  have : IsEmpty (childClusters H A) := by rw [h]; infer_instance
  rw [Fintype.sum_unique]; simp

theorem mem_childClusters {H : Finset (Finset X)} {A B : Finset X} :
    B ∈ childClusters H A ↔ B ∈ H ∧ B ⊂ A ∧ ∀ C ∈ H, B ⊂ C → ¬ C ⊂ A :=
  mem_filter

theorem IsHierarchy.childClusters_singleton {H : Finset (Finset X)} (hH : IsHierarchy H) (x : X) :
    childClusters H {x} = ∅ := by
  rw [childClusters, Finset.filter_eq_empty_iff]
  rintro B hB ⟨hBx, -⟩
  exact Finset.not_nonempty_empty (Finset.ssubset_singleton_iff.1 hBx ▸ hH.2.2.1 _ hB)

theorem IsHierarchy.disjoint_of_mem_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A B C : Finset X} (hB : B ∈ childClusters H A) (hC : C ∈ childClusters H A) (hBC : B ≠ C) :
    Disjoint B C := by
  rw [mem_childClusters] at hB hC
  rcases hH.2.2.2 B hB.1 C hC.1 with h | h | h
  · exact absurd hC.2.1 (hB.2.2 C hC.1 (lt_of_le_of_ne h hBC))
  · exact absurd hB.2.1 (hC.2.2 B hB.1 (lt_of_le_of_ne h hBC.symm))
  · exact h

theorem mem_sampledForest {s : L → X} {A : Finset X} {C : Finset L} :
    C ∈ sampledForest s A ↔ ∃ l, s l ∈ A ∧ {l} = C := by
  simp [sampledForest]

theorem singleton_mem_sampledForest {s : L → X} {A : Finset X} {l : L} :
    {l} ∈ sampledForest s A ↔ s l ∈ A := by
  simp [sampledForest]

lemma singleton_laminar (l : L) (D : Finset L) :
    {l} ⊆ D ∨ D ⊆ {l} ∨ Disjoint {l} D :=
  if h : l ∈ D then Or.inl (singleton_subset_iff.2 h)
  else Or.inr (Or.inr (disjoint_singleton_left.2 h))

theorem IsHierarchy.isForest_entering {H : Finset (Finset X)} (hH : IsHierarchy H) {s : L → X}
    {A : Finset X} (f : childClusters H A → Finset (Finset L))
    (hf : ∀ B, IsForest (f B) ∧ lineages (f B) = univ.filter (fun l => s l ∈ (B : Finset X))) :
    IsForest (univ.sup f ∪ sampledForest s A) ∧
      sampledForest s A ⊆ univ.sup f ∪ sampledForest s A ∧
      lineages (univ.sup f ∪ sampledForest s A) = univ.filter (fun l => s l ∈ A) := by
  have hsub (B : childClusters H A) {C} (hC : C ∈ f B) {l} (hl : l ∈ C) : s l ∈ (B : Finset X) := by
    have : l ∈ lineages (f B) := mem_lineages.2 ⟨C, hC, hl⟩
    rwa [(hf B).2, mem_filter, and_iff_right (mem_univ _)] at this
  refine ⟨⟨fun C hC => ?_, fun C hC D hD => ?_⟩, subset_union_right, ?_⟩
  · rcases mem_union.1 hC with hC | hC
    · obtain ⟨B, -, hCB⟩ := Finset.mem_sup.1 hC; exact (hf B).1.1 C hCB
    · exact (isForest_sampledForest s A).1 C hC
  · rcases mem_union.1 hD with hD' | hD'
    · rcases mem_union.1 hC with hC' | hC'
      · obtain ⟨B, -, hCB⟩ := Finset.mem_sup.1 hC'
        obtain ⟨B', -, hDB'⟩ := Finset.mem_sup.1 hD'
        by_cases hBB' : B = B'
        · subst hBB'; exact (hf B).1.2 C hCB D hDB'
        · refine Or.inr (Or.inr (Finset.disjoint_left.2 fun l hlC hlD => ?_))
          exact Finset.disjoint_left.1 (hH.disjoint_of_mem_childClusters B.2 B'.2
            (fun h => hBB' (Subtype.ext h))) (hsub B hCB hlC) (hsub B' hDB' hlD)
      · obtain ⟨l, -, rfl⟩ := mem_sampledForest.1 hC'; exact singleton_laminar l D
    · obtain ⟨l, -, rfl⟩ := mem_sampledForest.1 hD'
      rcases singleton_laminar l C with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h.symm)
  · ext l; rw [mem_lineages, mem_filter]
    refine ⟨fun ⟨C, hC, hlC⟩ => ⟨mem_univ _, ?_⟩, fun ⟨_, h⟩ =>
      ⟨{l}, mem_union_right _ (singleton_mem_sampledForest.2 h), mem_singleton_self l⟩⟩
    rcases mem_union.1 hC with hC | hC
    · obtain ⟨B, -, hCB⟩ := Finset.mem_sup.1 hC
      exact (mem_childClusters.1 B.2).2.1.1 (hsub B hCB hlC)
    · obtain ⟨l', hl', rfl⟩ := mem_sampledForest.1 hC
      exact mem_singleton.1 hlC ▸ hl'

theorem populationKernel_support {len : Finset X → ℝ} {A : Finset X} {F G : Finset (Finset L)}
    (hF : IsForest F) (h : populationKernel len A F G ≠ 0) :
    IsForest G ∧ F ⊆ G ∧ lineages G = lineages F := by
  unfold populationKernel at h
  have ⟨k, hk⟩ : ∃ k, (jumpMatrix ^ k) F G ≠ 0 := by
    split_ifs at h; exacts [⟨_, by rwa [← kingmanAbsorption_apply hF]⟩,
      ⟨_, right_ne_zero_of_mul (by rwa [← kingmanTransition_apply hF])⟩]
  obtain ⟨h1, h2, h3, -⟩ := jumpMatrix_pow_support hF hk; exact ⟨h1, h2, h3⟩

theorem populationKernel_nonneg {len : Finset X → ℝ} {A : Finset X} (hlen : A ≠ univ → 0 ≤ len A)
    {F : Finset (Finset L)} (hF : IsForest F) (G : Finset (Finset L)) :
    0 ≤ populationKernel len A F G := by
  unfold populationKernel
  split_ifs with hA; exacts [kingmanAbsorption_nonneg hF G, kingmanTransition_nonneg (hlen hA) F G]

theorem populationKernel_sum (len : Finset X → ℝ) (A : Finset X) {F : Finset (Finset L)}
    (hF : IsForest F) : ∑ G, populationKernel len A F G = 1 := by
  unfold populationKernel
  split_ifs with hA; exacts [kingmanAbsorption_sum hF, kingmanTransition_sum hF (len A)]

theorem forestDist_support {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) {A : Finset X} (hA : A ∈ H) {G : Finset (Finset L)}
    (hG : forestDist H len s A G ≠ 0) :
    IsForest G ∧ sampledForest s A ⊆ G ∧ lineages G = univ.filter (fun l => s l ∈ A) := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist] at hG
  obtain ⟨f, -, hf⟩ := Finset.exists_ne_zero_of_sum_ne_zero hG
  have hprod := left_ne_zero_of_mul hf
  obtain ⟨hF, hSF, hLF⟩ := hH.isForest_entering f fun B =>
    let hB := mem_childClusters.1 B.2
    let ⟨h1, _, h3⟩ := ih B hB.2.1 hB.1 (Finset.prod_ne_zero_iff.1 hprod B (mem_univ _))
    ⟨h1, h3⟩
  obtain ⟨hG1, hG2, hG3⟩ := populationKernel_support hF (right_ne_zero_of_mul hf)
  exact ⟨hG1, hSF.trans hG2, hG3.trans hLF⟩

private theorem isForest_entering_of_prod_ne_zero {H : Finset (Finset X)} (hH : IsHierarchy H)
    {len : Finset X → ℝ} {s : L → X} {A : Finset X} {f : childClusters H A → Finset (Finset L)}
    (hprod : ∏ B : childClusters H A, forestDist H len s B (f B) ≠ 0) :
    IsForest (univ.sup f ∪ sampledForest s A) :=
  (hH.isForest_entering f fun B =>
    let ⟨h1, _, h3⟩ := forestDist_support hH len s (mem_childClusters.1 B.2).1
      (Finset.prod_ne_zero_iff.1 hprod B (mem_univ _)); ⟨h1, h3⟩).1

theorem forestDist_nonneg_of_ne_univ {H : Finset (Finset X)} (hH : IsHierarchy H)
    {len : Finset X → ℝ} (hlen : ∀ A ∈ H, A ≠ univ → 0 ≤ len A) (s : L → X) {A : Finset X}
    (hA : A ∈ H) (G : Finset (Finset L)) : 0 ≤ forestDist H len s A G := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist]
  refine Finset.sum_nonneg fun f _ => ?_
  by_cases hprod : ∏ B : childClusters H A, forestDist H len s B (f B) = 0
  · rw [hprod, zero_mul]
  · exact mul_nonneg (Finset.prod_nonneg fun B _ =>
      ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1 _)
      (populationKernel_nonneg (hlen A hA) (isForest_entering_of_prod_ne_zero hH hprod) G)

theorem forestDist_sum {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) {A : Finset X} (hA : A ∈ H) : ∑ G, forestDist H len s A G = 1 := by
  induction A using Finset.strongInduction with
  | H A ih =>
  simp_rw [show ∀ G, forestDist H len s A G = _ from fun G => by rw [forestDist]]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hterm (f : childClusters H A → Finset (Finset L)) :
      (∏ B : childClusters H A, forestDist H len s B (f B)) *
        ∑ G, populationKernel len A (univ.sup f ∪ sampledForest s A) G =
      ∏ B : childClusters H A, forestDist H len s B (f B) := by
    by_cases hprod : ∏ B : childClusters H A, forestDist H len s B (f B) = 0
    · rw [hprod, zero_mul]
    · rw [populationKernel_sum len A (isForest_entering_of_prod_ne_zero hH hprod), mul_one]
  simp_rw [hterm, ← Fintype.prod_sum]
  exact Finset.prod_eq_one fun B _ => ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1

theorem enteringDist_support {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) {A : Finset X} {F : Finset (Finset L)} (hF : enteringDist H len s A F ≠ 0) :
    IsForest F := by
  unfold enteringDist at hF
  obtain ⟨f, -, hf⟩ := Finset.exists_ne_zero_of_sum_ne_zero hF
  split_ifs at hf with hfF
  · exact hfF ▸ isForest_entering_of_prod_ne_zero hH hf
  · exact absurd rfl hf

theorem IsHierarchy.exists_mem_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A : Finset X} (hA : 2 ≤ #A) {x : X} (hx : x ∈ A) : ∃ B ∈ childClusters H A, x ∈ B := by
  have hxA : ({x} : Finset X) ⊂ A :=
    (singleton_subset_iff.2 hx).ssubset_of_ne (by rintro rfl; simp at hA)
  obtain ⟨B, hB, hmax⟩ := (H.filter fun C => x ∈ C ∧ C ⊂ A).exists_max_image card
    ⟨{x}, mem_filter.2 ⟨hH.2.1 x, mem_singleton_self x, hxA⟩⟩
  rw [mem_filter] at hB
  exact ⟨B, mem_childClusters.2 ⟨hB.1, hB.2.2, fun C hC hBC hCA =>
    absurd (card_lt_card hBC) (not_lt.2 (hmax C (mem_filter.2 ⟨hC, hBC.subset hB.2.1, hCA⟩)))⟩,
    hB.2.1⟩

theorem IsHierarchy.two_le_card_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A : Finset X} (hA : 2 ≤ #A) : 2 ≤ #(childClusters H A) := by
  by_contra hlt
  have hle : #(childClusters H A) ≤ 1 := by omega
  obtain ⟨x, hx⟩ : A.Nonempty := card_pos.1 (by omega)
  obtain ⟨B, hB, -⟩ := hH.exists_mem_childClusters hA hx
  rw [Finset.card_le_one_iff] at hle
  exact not_subset_of_ssubset (mem_childClusters.1 hB).2.1 fun y hy =>
    let ⟨_, hC, hyC⟩ := hH.exists_mem_childClusters hA hy; hle hC hB ▸ hyC

theorem IsHierarchy.subset_or_subset_of_mem {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A B : Finset X} (hA : A ∈ H) (hB : B ∈ H) {x : X} (hxA : x ∈ A) (hxB : x ∈ B) :
    A ⊆ B ∨ B ⊆ A :=
  (or_assoc.2 (hH.2.2.2 A hA B hB)).resolve_right (not_disjoint_iff.2 ⟨x, hxA, hxB⟩)

theorem IsHierarchy.exists_mem_childClusters_superset {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A E : Finset X} (hE : E ∈ H) (hEA : E ⊂ A) : ∃ B ∈ childClusters H A, E ⊆ B := by
  obtain ⟨x, hx⟩ := hH.2.2.1 E hE
  have := card_pos.2 ⟨x, hx⟩; have := card_lt_card hEA
  obtain ⟨B, hB, hxB⟩ := hH.exists_mem_childClusters (by omega) (hEA.subset hx)
  refine ⟨B, hB, (hH.subset_or_subset_of_mem hE (mem_childClusters.1 hB).1 hx hxB).elim id
    fun h => h.eq_or_ssubset.elim (·.symm.subset) fun h' =>
      absurd hEA ((mem_childClusters.1 hB).2.2 E hE h')⟩

theorem forestDist_singleton_of_card_le_one {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) {s : L → X} {x : X} (hx : #(univ.filter fun l => s l = x) ≤ 1)
    (G : Finset (Finset L)) :
    forestDist H len s {x} G = if G = sampledForest s {x} then 1 else 0 := by
  rw [forestDist_of_childClusters_eq_empty (hH.childClusters_singleton x), populationKernel]
  have hF := isForest_sampledForest s ({x} : Finset X)
  have hk : #(roots (sampledForest s {x})) ≤ 1 :=
    (card_le_card (roots_subset _)).trans (card_image_le.trans (by simpa using hx))
  by_cases hxu : ({x} : Finset X) = univ <;> [rw [ite_eq_left hxu]; rw [ite_eq_right hxu]]
  exacts [kingmanAbsorption_of_card_roots_le_one hF hk G,
    kingmanTransition_of_card_roots_le_one hF hk _ G]

theorem forestDist_id_singleton {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) (x : X) (G : Finset (Finset X)) :
    forestDist H len id {x} G = if G = {{x}} then 1 else 0 := by
  rw [forestDist_singleton_of_card_le_one hH len (by simp [Finset.filter_eq']) G,
    show sampledForest (id : X → X) {x} = {{x}} by ext; simp [sampledForest, eq_comm]]

theorem unrootedDist_nonneg (σ : SpeciesTree X) (s : L → X) (T : Finset (Finset L)) :
    0 ≤ σ.unrootedDist s T :=
  sum_nonneg fun G _ => by
    split_ifs; exacts [forestDist_nonneg_of_ne_univ σ.isHierarchy
      (fun A hA hAu => (σ.length_pos A hA hAu).le) s σ.univ_mem G, le_rfl]

theorem unrootedDist_sum (σ : SpeciesTree X) (s : L → X) : ∑ T, σ.unrootedDist s T = 1 := by
  unfold SpeciesTree.unrootedDist
  rw [sum_comm]
  simp_rw [sum_ite_eq, mem_univ, ite_true]
  exact forestDist_sum σ.isHierarchy σ.length s σ.univ_mem



end ADR11
