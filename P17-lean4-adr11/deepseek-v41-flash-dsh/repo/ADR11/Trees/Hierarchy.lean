module

public import ADR11.MSC.Basic

/-!
# Combinatorics of rooted species trees (hierarchies)

## Main results

* `SpeciesTree.mem_clusters_of_triples`: a set `A` with at least two taxa is a cluster as soon as,
  for all `a, a' ∈ A` and `b ∉ A`, some cluster contains `a` and `a'` but not `b` (rooted
  triples determine a rooted tree).
* `SpeciesTree.restrict_isBinary`: the induced subtree of a binary species tree is binary.
* `SpeciesTree.sameUnrootedMetricTree_of_card_le_three`: on at most three taxa all unrooted metric
  species trees agree (there is no internal edge).
* `SpeciesTree.restrict_unroot`, `SpeciesTree.restrict_unrootedLength`: induced subtrees and
  unrooting commute, and the unrooted length of a split of `σ(S)` is the sum of the unrooted
  lengths of the splits of `σ` that induce it.

## General facts on hierarchies

(The children of a cluster are also treated in `ADR11.MSC.Basic`: `mem_childClusters`,
`IsHierarchy.disjoint_of_mem_childClusters`, `IsHierarchy.exists_mem_childClusters`,
`IsHierarchy.sup_childClusters`, `IsHierarchy.two_le_card_childClusters`,
`IsHierarchy.childClusters_eq_pair`, `SpeciesTree.isBinary_iff_card_childClusters`.)

* `IsHierarchy.subset_or_subset_of_mem`: clusters with a common element are nested.
* `lca H T`: the smallest cluster containing `T`; `IsHierarchy.lca_mem`, `subset_lca`,
  `lca_subset`, `IsHierarchy.lca_eq_iff`, `IsHierarchy.lca_pair_eq_of_mem_childClusters`.
* `IsHierarchy.subset_of_mem_childClusters`, `IsHierarchy.existsUnique_mem_childClusters`,
  `IsHierarchy.exists_mem_childClusters_superset`: the children of a cluster partition it, and
  every cluster strictly inside it lies inside a child.
* `parentCluster H A`: the parent of a cluster; `IsHierarchy.parentCluster_mem`,
  `IsHierarchy.ssubset_parentCluster`, `parentCluster_subset`,
  `IsHierarchy.mem_childClusters_parentCluster`, `IsHierarchy.existsUnique_parent`.
* `IsHierarchy.mem_of_triples`: rooted triples determine the clusters of a hierarchy.
* `mem_restrictClusters`, `IsHierarchy.mem_restrictClusters_iff`, `subtype_lca_eq`: the clusters of
  an induced tree are the nonempty traces of clusters, and each is the trace of the smallest cluster
  containing it; `SpeciesTree.restrictLength_subtype_eq`.
* `mem_unroot`, `compl_mem_unroot`, `IsHierarchy.compatible_of_mem_unroot` (the splits of `σ⁻` are
  pairwise compatible), `mem_restrictSplits`, `SpeciesTree.unrootedLength_compl`,
  `SpeciesTree.restrict_unrootedLength_eq_of_unique` (a split of `σ⁻(S)` induced by a single split
  of `σ⁻` has the same length).
* `SpeciesTree.SameRootedMetricTree.refl`/`symm`/`trans`, and the same for
  `SameUnrootedMetricTree`.
-/

@[expose] public section

namespace ADR11

set_option linter.unusedSectionVars false

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Clusters with a common element are nested -/

namespace IsHierarchy

variable {H : Fam X}

/-- Two clusters of a hierarchy with a common element are nested. -/
theorem subset_or_subset_of_mem (hH : IsHierarchy H) {A B : Finset X} (hA : A ∈ H) (hB : B ∈ H)
    {x : X} (hxA : x ∈ A) (hxB : x ∈ B) : A ⊆ B ∨ B ⊆ A := by
  rcases hH.2.2.2 A hA B hB with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd hxB (disjoint_left.1 h hxA)

/-- Two clusters of a hierarchy that are not disjoint are nested. -/
theorem subset_or_subset_of_not_disjoint (hH : IsHierarchy H) {A B : Finset X} (hA : A ∈ H)
    (hB : B ∈ H) (hAB : ¬ Disjoint A B) : A ⊆ B ∨ B ⊆ A := by
  obtain ⟨x, hxA, hxB⟩ := not_disjoint_iff.1 hAB
  exact hH.subset_or_subset_of_mem hA hB hxA hxB

/-- The clusters of a hierarchy containing a common element `x` and satisfying `p` are closed
under union (the union of two of them is one of them). -/
private theorem hier_sup_mem (hH : IsHierarchy H) (x : X) (p : Finset X → Prop) :
    ∀ C ∈ {C | C ∈ H ∧ x ∈ C ∧ p C}, ∀ D ∈ {C | C ∈ H ∧ x ∈ C ∧ p C},
      C ⊔ D ∈ {C | C ∈ H ∧ x ∈ C ∧ p C} := by
  rintro C hC D hD
  rcases hH.subset_or_subset_of_mem hC.1 hD.1 hC.2.1 hD.2.1 with h | h
  · rwa [sup_eq_right.2 h]
  · rwa [sup_eq_left.2 h]

/-- The clusters of a hierarchy containing a common element `x` and satisfying `p` are closed
under intersection. -/
private theorem hier_inf_mem (hH : IsHierarchy H) (x : X) (p : Finset X → Prop) :
    ∀ C ∈ {C | C ∈ H ∧ x ∈ C ∧ p C}, ∀ D ∈ {C | C ∈ H ∧ x ∈ C ∧ p C},
      C ⊓ D ∈ {C | C ∈ H ∧ x ∈ C ∧ p C} := by
  rintro C hC D hD
  rcases hH.subset_or_subset_of_mem hC.1 hD.1 hC.2.1 hD.2.1 with h | h
  · rwa [inf_eq_left.2 h]
  · rwa [inf_eq_right.2 h]

end IsHierarchy

/-! ### The smallest cluster containing a set -/

/-- The smallest cluster of `H` containing `T`: the intersection of the clusters of `H` that
contain `T`. For a hierarchy `H` and a nonempty `T` it is a cluster of `H` (`IsHierarchy.lca_mem`),
the cluster of the most recent common ancestor of the taxa in `T`. -/
def lca (H : Fam X) (T : Finset X) : Finset X :=
  (H.filter (T ⊆ ·)).inf id

/-- A set is contained in the smallest cluster containing it. -/
theorem subset_lca (H : Fam X) (T : Finset X) : T ⊆ lca H T :=
  Finset.le_inf fun _ hC => (mem_filter.1 hC).2

/-- The smallest cluster containing `T` is contained in every cluster containing `T`. -/
theorem lca_subset {H : Fam X} {T C : Finset X} (hC : C ∈ H) (hTC : T ⊆ C) :
    lca H T ⊆ C :=
  Finset.inf_le (f := id) (mem_filter.2 ⟨hC, hTC⟩)

namespace IsHierarchy

variable {H : Fam X}

/-- In a hierarchy, the smallest cluster containing a nonempty set is a cluster. -/
theorem lca_mem (hH : IsHierarchy H) {T : Finset X} (hT : T.Nonempty) : lca H T ∈ H := by
  obtain ⟨t, ht⟩ := hT
  have := Finset.inf_mem {C | C ∈ H ∧ t ∈ C ∧ T ⊆ C} ⟨hH.1, mem_univ t, subset_univ T⟩
    (hier_inf_mem hH t (T ⊆ ·)) (H.filter (T ⊆ ·)) id
    (fun C hC => ⟨(mem_filter.1 hC).1, (mem_filter.1 hC).2 ht, (mem_filter.1 hC).2⟩)
  exact this.1

/-- Characterization of the smallest cluster containing a nonempty set. -/
theorem lca_eq_iff (hH : IsHierarchy H) {T C : Finset X} (hT : T.Nonempty) :
    lca H T = C ↔ C ∈ H ∧ T ⊆ C ∧ ∀ D ∈ H, T ⊆ D → C ⊆ D := by
  constructor
  · rintro rfl
    exact ⟨hH.lca_mem hT, subset_lca H T, fun D hD hTD => lca_subset hD hTD⟩
  · rintro ⟨hC, hTC, hmin⟩
    exact Subset.antisymm (lca_subset hC hTC) (hmin _ (hH.lca_mem hT) (subset_lca H T))

end IsHierarchy

/-! ### Children -/

namespace IsHierarchy

variable {H : Fam X}

/-- A cluster strictly contained in `A` that meets a child `B` of `A` is contained in `B`. -/
theorem subset_of_mem_childClusters (hH : IsHierarchy H) {A B C : Finset X}
    (hB : B ∈ childClusters H A) (hC : C ∈ H) (hCA : C ⊂ A) (hBC : ¬ Disjoint B C) : C ⊆ B := by
  rw [mem_childClusters] at hB
  rcases hH.subset_or_subset_of_not_disjoint hB.1 hC hBC with h | h
  · by_contra hCB
    exact hB.2.2 C hC (ssubset_of_subset_not_subset h hCB) hCA
  · exact h

/-- Every element `x` of a cluster `A ≠ {x}` lies in a child of `A` (the cluster `A` need not be a
member of `H`). -/
theorem exists_mem_childClusters_of_ne (hH : IsHierarchy H) {A : Finset X} {x : X} (hx : x ∈ A)
    (hAx : A ≠ {x}) : ∃ B ∈ childClusters H A, x ∈ B := by
  set F := H.filter (fun C => x ∈ C ∧ C ⊂ A)
  have hF : F.Nonempty := ⟨{x}, mem_filter.2 ⟨hH.2.1 x, mem_singleton_self x,
    ssubset_of_subset_not_subset (singleton_subset_iff.2 hx)
      (fun h => hAx (Subset.antisymm h (singleton_subset_iff.2 hx)))⟩⟩
  have hmem : F.sup' hF id ∈ {C | C ∈ H ∧ x ∈ C ∧ C ⊂ A} :=
    Finset.sup'_mem _ (hier_sup_mem hH x (· ⊂ A)) F hF id (fun C hC => mem_filter.1 hC)
  refine ⟨F.sup' hF id, mem_childClusters.2 ⟨hmem.1, hmem.2.2, fun C hC hBC hCA => ?_⟩,
    hmem.2.1⟩
  have : C ⊆ F.sup' hF id :=
    Finset.le_sup' id (mem_filter.2 ⟨hC, hBC.subset hmem.2.1, hCA⟩)
  exact not_subset_of_ssubset hBC this

/-- A cluster strictly contained in `A` is contained in a child of `A`. -/
theorem exists_mem_childClusters_superset (hH : IsHierarchy H) {A B : Finset X} (hB : B ∈ H)
    (hBA : B ⊂ A) : ∃ C ∈ childClusters H A, B ⊆ C := by
  obtain ⟨b, hb⟩ := hH.2.2.1 B hB
  have hAb : A ≠ {b} := by
    rintro rfl
    exact not_subset_of_ssubset hBA (singleton_subset_iff.2 hb)
  obtain ⟨C, hC, hbC⟩ := hH.exists_mem_childClusters_of_ne (hBA.subset hb) hAb
  exact ⟨C, hC, hH.subset_of_mem_childClusters hC hB hBA (not_disjoint_iff.2 ⟨b, hbC, hb⟩)⟩

/-- Two taxa in different children of a cluster `A` have `A` as their smallest common cluster. -/
theorem lca_pair_eq_of_mem_childClusters (hH : IsHierarchy H) {A B₁ B₂ : Finset X} (hA : A ∈ H)
    (hB₁ : B₁ ∈ childClusters H A) (hB₂ : B₂ ∈ childClusters H A) (hne : B₁ ≠ B₂) {a₁ a₂ : X}
    (ha₁ : a₁ ∈ B₁) (ha₂ : a₂ ∈ B₂) : lca H {a₁, a₂} = A := by
  have hA₁ : a₁ ∈ A := (mem_childClusters.1 hB₁).2.1.subset ha₁
  have hA₂ : a₂ ∈ A := (mem_childClusters.1 hB₂).2.1.subset ha₂
  refine (hH.lca_eq_iff (insert_nonempty a₁ {a₂})).2 ⟨hA, ?_, fun D hD hsub => ?_⟩
  · rw [insert_subset_iff, singleton_subset_iff]
    exact ⟨hA₁, hA₂⟩
  · rw [insert_subset_iff, singleton_subset_iff] at hsub
    rcases hH.subset_or_subset_of_mem hD hA hsub.1 hA₁ with h | h
    · by_contra hDA
      have hD' : D ⊂ A := ssubset_of_subset_not_subset h fun h' => hDA h'
      have h₁ := hH.subset_of_mem_childClusters hB₁ hD hD'
        (not_disjoint_iff.2 ⟨a₁, ha₁, hsub.1⟩)
      exact disjoint_left.1 (hH.disjoint_of_mem_childClusters hB₁ hB₂ hne) (h₁ hsub.2) ha₂
    · exact h

end IsHierarchy

/-! ### Parents -/

namespace IsHierarchy

variable {H : Fam X}

end IsHierarchy

/-! ### Induced subtrees -/

namespace SpeciesTree

/-- The clusters of the induced tree `σ(S)`. -/
@[simp] theorem restrict_clusters (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    (σ.restrict S hS).clusters = restrictClusters S σ.clusters := rfl

/-- The edge lengths of the induced tree `σ(S)`. -/
@[simp] theorem restrict_length (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    (σ.restrict S hS).length = σ.restrictLength S := rfl

end SpeciesTree

/-- The clusters of the induced tree on `S` are the nonempty traces on `S` of the clusters. -/
theorem mem_restrictClusters {S : Finset X} {H : Fam X} {C : Finset S} :
    C ∈ restrictClusters S H ↔ ∃ A ∈ H, (A ∩ S).Nonempty ∧ A.subtype (· ∈ S) = C := by
  unfold restrictClusters
  rw [mem_image]
  simp only [mem_filter, and_assoc]

/-- The splits of the induced unrooted tree on `S` are the traces of the splits whose two sides
both meet `S`. -/
theorem mem_restrictSplits {S : Finset X} {T : Fam X} {C : Finset S} :
    C ∈ restrictSplits S T ↔
      ∃ A ∈ T, (A ∩ S).Nonempty ∧ (Aᶜ ∩ S).Nonempty ∧ A.subtype (· ∈ S) = C := by
  unfold restrictSplits
  rw [mem_image]
  simp only [mem_filter, and_assoc]

/-- The trace of `A` on `S` is nonempty if and only if `A` meets `S`. -/
theorem subtype_nonempty_iff {S A : Finset X} :
    (A.subtype (· ∈ S)).Nonempty ↔ (A ∩ S).Nonempty := by
  constructor
  · rintro ⟨⟨x, hxS⟩, hx⟩
    exact ⟨x, mem_inter.2 ⟨mem_subtype.1 hx, hxS⟩⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨x, (mem_inter.1 hx).2⟩, mem_subtype.2 (mem_inter.1 hx).1⟩

/-- The trace of the complement is the complement of the trace. -/
theorem subtype_compl {S : Finset X} (A : Finset X) :
    Aᶜ.subtype (· ∈ S) = (A.subtype (· ∈ S))ᶜ := by
  ext x
  simp [mem_subtype, mem_compl]

/-- The trace of `A` on `S` is not all of `S` if and only if `Aᶜ` meets `S`. -/
theorem subtype_ne_univ_iff {S A : Finset X} :
    A.subtype (· ∈ S) ≠ univ ↔ (Aᶜ ∩ S).Nonempty := by
  rw [← subtype_nonempty_iff, subtype_compl, Ne, ← compl_eq_empty_iff,
    ← not_nonempty_iff_eq_empty, not_not]

/-- Mapping the trace of `A` on `S` (a set of elements of `S`) back to `X` gives `A ∩ S`. -/
theorem map_subtype_eq_inter (S A : Finset X) :
    (A.subtype (· ∈ S)).map (Function.Embedding.subtype _) = A ∩ S := by
  rw [subtype_map, filter_mem_eq_inter]

/-- The trace of a cluster meeting `S` is a cluster of the induced tree on `S`. -/
theorem subtype_mem_restrictClusters {S : Finset X} {H : Fam X} {A : Finset X}
    (hA : A ∈ H) (hAS : (A ∩ S).Nonempty) : A.subtype (· ∈ S) ∈ restrictClusters S H :=
  mem_restrictClusters.2 ⟨A, hA, hAS, rfl⟩

/-- A cluster `C` of the induced tree on `S` is the trace of the smallest cluster containing it. -/
theorem subtype_lca_eq {S : Finset X} {H : Fam X} {C : Finset S}
    (hC : C ∈ restrictClusters S H) :
    (lca H (C.map (Function.Embedding.subtype _))).subtype (· ∈ S) = C := by
  obtain ⟨A, hA, -, rfl⟩ := mem_restrictClusters.1 hC
  apply Subset.antisymm
  · intro x hx
    rw [mem_subtype] at hx ⊢
    apply lca_subset hA _ hx
    rw [map_subtype_eq_inter]
    exact inter_subset_left
  · intro x hx
    rw [mem_subtype]
    apply subset_lca
    exact mem_map_of_mem _ hx

namespace SpeciesTree

/-- The length of the edge above a cluster `A ∩ S` of the induced tree, when `A` is the only
cluster of `σ` with this trace. -/
theorem restrictLength_subtype_eq (σ : SpeciesTree X) {S A : Finset X} (hA : A ∈ σ.clusters)
    (hAu : A ≠ univ)
    (h : ∀ B ∈ σ.clusters, B.subtype (· ∈ S) = A.subtype (· ∈ S) → B = A) :
    σ.restrictLength S (A.subtype (· ∈ S)) = σ.length A := by
  unfold restrictLength
  rw [Finset.sum_eq_single_of_mem A (mem_filter.2 ⟨hA, hAu, rfl⟩)]
  intro B hB hBA
  exact absurd (h B (mem_filter.1 hB).1 (mem_filter.1 hB).2.2) hBA

end SpeciesTree

/-! ### Unrooted trees -/

section Unroot

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The sides of the splits of the unrooted tree of `G`: the non-root clusters of `G` and their
complements. -/
theorem mem_unroot {G : Fam L} {A : Finset L} :
    A ∈ unroot G ↔ (A ∈ G ∧ A ≠ univ) ∨ (Aᶜ ∈ G ∧ Aᶜ ≠ univ) := absorb_mem_unroot
/-- The unrooted tree of `G` is closed under complements. -/
theorem compl_mem_unroot {G : Fam L} {A : Finset L} :
    Aᶜ ∈ unroot G ↔ A ∈ unroot G := by
  rw [mem_unroot, mem_unroot, compl_compl, or_comm]

end Unroot

/-! ### Rooted triples -/

/-- Rooted triples determine the clusters of a hierarchy: if for all `a, a' ∈ A` and `b ∉ A` some
cluster of `H` contains `a` and `a'` but not `b`, then `A` is a cluster of `H`. -/
theorem IsHierarchy.mem_of_triples {H : Fam X} (hH : IsHierarchy H) {A : Finset X}
    (hA : A.Nonempty) (h : ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∉ A, ∃ C ∈ H, a ∈ C ∧ a' ∈ C ∧ b ∉ C) :
    A ∈ H := by
  obtain ⟨a, ha⟩ := hA
  suffices hsub : lca H A ⊆ A by
    rw [← Subset.antisymm hsub (subset_lca _ A)]
    exact hH.lca_mem ⟨a, ha⟩
  intro b hbL
  by_contra hbA
  -- the clusters containing `a` but not `b` form a chain; its largest member contains `A`
  set F := H.filter (fun C => a ∈ C ∧ b ∉ C)
  obtain ⟨C₀, hC₀, haC₀, -, hbC₀⟩ := h a ha a ha b hbA
  have hF : F.Nonempty := ⟨C₀, mem_filter.2 ⟨hC₀, haC₀, hbC₀⟩⟩
  have hU : F.sup' hF id ∈ {C | C ∈ H ∧ a ∈ C ∧ b ∉ C} :=
    Finset.sup'_mem _ (IsHierarchy.hier_sup_mem hH a (b ∉ ·)) F hF id
      (fun C hC => mem_filter.1 hC)
  have hAU : A ⊆ F.sup' hF id := fun a' ha' => by
    obtain ⟨C, hC, haC, ha'C, hbC⟩ := h a ha a' ha' b hbA
    exact Finset.le_sup' id (mem_filter.2 ⟨hC, haC, hbC⟩) ha'C
  exact hU.2.2 (lca_subset hU.1 hAU hbL)

namespace SpeciesTree

/-- Rooted triples determine the clusters: if for all `a, a' ∈ A` and `b ∉ A` some cluster of
`σ` contains `a` and `a'` but not `b`, then `A` is a cluster of `σ`. -/
theorem mem_clusters_of_triples (σ : SpeciesTree X) {A : Finset X} (hA : A.Nonempty)
    (h : ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∉ A, ∃ C ∈ σ.clusters, a ∈ C ∧ a' ∈ C ∧ b ∉ C) :
    A ∈ σ.clusters :=
  σ.isHierarchy.mem_of_triples hA h

/-! ### Induced subtrees of binary trees -/

/-- The induced subtree of a binary species tree is binary. -/
theorem restrict_isBinary {σ : SpeciesTree X} (hσ : σ.IsBinary) (S : Finset X)
    (hS : S.Nonempty) : (σ.restrict S hS).IsBinary := by
  intro C hC hC2
  rw [restrict_clusters] at hC ⊢
  have hH := σ.isHierarchy
  -- `C`, as a set of taxa, and the smallest cluster `lca σ.clusters T` containing it
  set T := C.map (Function.Embedding.subtype (· ∈ S))
  have hTC : #T = #C := card_map _
  have hT : T.Nonempty := card_pos.1 (by omega)
  have hTS : T ⊆ S := fun x hx => by
    obtain ⟨y, -, rfl⟩ := mem_map.1 hx
    exact y.2
  have hL : lca σ.clusters T ∈ σ.clusters := hH.lca_mem hT
  have hLC : (lca σ.clusters T).subtype (· ∈ S) = C := subtype_lca_eq hC
  have hL2 : 2 ≤ #(lca σ.clusters T) := by
    have := card_le_card (subset_lca σ.clusters T)
    omega
  obtain ⟨B, hB, D, hD, hBD, hBDL⟩ := hσ _ hL hL2
  -- `T` is contained in neither part, so both traces are nonempty
  have hnot : ∀ E ∈ σ.clusters, E ⊆ lca σ.clusters T → E ≠ lca σ.clusters T → ¬ T ⊆ E :=
    fun E hE hEL hne hTE => hne (Subset.antisymm hEL (lca_subset hE hTE))
  have hBne : B ≠ lca σ.clusters T := by
    intro e
    obtain ⟨d, hd⟩ := σ.nonempty_of_mem D hD
    exact disjoint_left.1 hBD (e ▸ hBDL ▸ mem_union_right B hd) hd
  have hDne : D ≠ lca σ.clusters T := by
    intro e
    obtain ⟨b, hb⟩ := σ.nonempty_of_mem B hB
    exact disjoint_left.1 hBD hb (e ▸ hBDL ▸ mem_union_left D hb)
  have hBS : (B ∩ S).Nonempty := by
    obtain ⟨t, htT, htD⟩ := not_subset.1 (hnot D hD (hBDL ▸ subset_union_right) hDne)
    have htL : t ∈ B ∪ D := hBDL ▸ subset_lca _ T htT
    exact ⟨t, mem_inter.2 ⟨(mem_union.1 htL).resolve_right htD, hTS htT⟩⟩
  have hDS : (D ∩ S).Nonempty := by
    obtain ⟨t, htT, htB⟩ := not_subset.1 (hnot B hB (hBDL ▸ subset_union_left) hBne)
    have htL : t ∈ B ∪ D := hBDL ▸ subset_lca _ T htT
    exact ⟨t, mem_inter.2 ⟨(mem_union.1 htL).resolve_left htB, hTS htT⟩⟩
  refine ⟨B.subtype (· ∈ S), subtype_mem_restrictClusters hB hBS,
    D.subtype (· ∈ S), subtype_mem_restrictClusters hD hDS, ?_, ?_⟩
  · exact disjoint_left.2 fun x hxB hxD =>
      disjoint_left.1 hBD (mem_subtype.1 hxB) (mem_subtype.1 hxD)
  · rw [← hLC, ← hBDL]
    ext x
    simp only [mem_union, mem_subtype]

/-! ### Agreement of metric trees -/

theorem SameRootedMetricTree.symm {σ σ' : SpeciesTree X} (h : σ.SameRootedMetricTree σ') :
    σ'.SameRootedMetricTree σ :=
  ⟨h.1.symm, fun A hA h2 hu => (h.2 A (h.1 ▸ hA) h2 hu).symm⟩

theorem SameUnrootedMetricTree.symm {σ σ' : SpeciesTree X} (h : σ.SameUnrootedMetricTree σ') :
    σ'.SameUnrootedMetricTree σ :=
  ⟨h.1.symm, fun A hA h2 h2' => (h.2 A (h.1 ▸ hA) h2 h2').symm⟩

/-! ### Unrooting induced subtrees -/

/-- The unrooted topology of an induced subtree is the induced unrooted topology. -/
theorem restrict_unroot (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    unroot (σ.restrict S hS).clusters = restrictSplits S (unroot σ.clusters) := by
  ext C
  rw [mem_unroot, restrict_clusters, mem_restrictSplits]
  constructor
  · rintro (⟨hC, hCu⟩ | ⟨hC, hCu⟩)
    · obtain ⟨A, hA, hAS, rfl⟩ := mem_restrictClusters.1 hC
      refine ⟨A, mem_unroot.2 (Or.inl ⟨hA, ?_⟩), hAS, subtype_ne_univ_iff.1 hCu, rfl⟩
      rintro rfl
      exact hCu (subtype_univ _)
    · obtain ⟨A, hA, hAS, hAC⟩ := mem_restrictClusters.1 hC
      have hAu : A ≠ univ := by
        rintro rfl
        exact hCu (hAC ▸ subtype_univ _)
      refine ⟨Aᶜ, compl_mem_unroot.2 (mem_unroot.2 (Or.inl ⟨hA, hAu⟩)),
        subtype_ne_univ_iff.1 (hAC ▸ hCu), by rwa [compl_compl], ?_⟩
      rw [subtype_compl, hAC, compl_compl]
  · rintro ⟨A, hA, hAS, hAcS, rfl⟩
    rcases mem_unroot.1 hA with ⟨hA', -⟩ | ⟨hA', -⟩
    · exact Or.inl ⟨subtype_mem_restrictClusters hA' hAS, subtype_ne_univ_iff.2 hAcS⟩
    · refine Or.inr ⟨?_, ?_⟩
      · rw [← subtype_compl]
        exact subtype_mem_restrictClusters hA' hAcS
      · rw [← subtype_compl]
        exact subtype_ne_univ_iff.2 (by rwa [compl_compl])

/-- The length of an internal edge of the unrooted induced subtree `σ⁻(S)`: the sum of the
unrooted lengths of the splits of `σ⁻` that induce its split. -/
theorem restrict_unrootedLength (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty)
    (C : Finset S) (hC₁ : 2 ≤ #C)
    (hC₂ : 2 ≤ #Cᶜ) :
    (σ.restrict S hS).unrootedLength C =
      (1 / 2 : ℝ) * ∑ A ∈ unroot σ.clusters with A.subtype (· ∈ S) = C ∨ A.subtype (· ∈ S) = Cᶜ,
        σ.unrootedLength A := by
  have : Nonempty X := ⟨hS.choose⟩
  have hCne : C.Nonempty := card_pos.1 (by omega)
  have hCcne : Cᶜ.Nonempty := card_pos.1 (by omega)
  have hCu : C ≠ univ := fun e => by
    rw [e, compl_univ] at hCcne
    exact not_nonempty_empty hCcne
  have hCcu : Cᶜ ≠ univ := (compl_ne_univ_iff_nonempty C).2 hCne
  -- `p A`: the trace of `A` is a side of the split `C | Cᶜ`
  set p : Finset X → Prop := fun A => A.subtype (· ∈ S) = C ∨ A.subtype (· ∈ S) = Cᶜ with hp
  have hpc : ∀ A, p Aᶜ ↔ p A := by
    intro A
    simp only [hp, subtype_compl, compl_inj_iff]
    rw [compl_eq_comm, eq_comm (a := Cᶜ)]
    exact or_comm
  set M := ∑ A ∈ σ.clusters with A ≠ univ ∧ p A, σ.length A with hM
  -- the left side is `M`: group the clusters of `σ` by their trace
  have hL : (σ.restrict S hS).unrootedLength C = M := by
    unfold unrootedLength
    rw [restrict_clusters, restrict_length, hM]
    symm
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun A => A.subtype (· ∈ S))
      (t := (restrictClusters S σ.clusters).filter (fun D => D ≠ univ ∧ (D = C ∨ D = Cᶜ)))]
    · apply Finset.sum_congr rfl
      intro D hD
      unfold restrictLength
      rw [filter_filter]
      refine Finset.sum_congr (filter_congr fun A _ => ?_) fun _ _ => rfl
      have hD' := (mem_filter.1 hD).2.2
      constructor
      · rintro ⟨⟨h2, -⟩, h3⟩
        exact ⟨h2, h3⟩
      · rintro ⟨h2, h3⟩
        have hpA : p A := by
          show A.subtype (· ∈ S) = C ∨ A.subtype (· ∈ S) = Cᶜ
          rw [h3]
          exact hD'
        exact ⟨⟨h2, hpA⟩, h3⟩
    · intro A hA
      obtain ⟨hA1, -, hA3⟩ := mem_filter.1 hA
      refine mem_filter.2 ⟨mem_restrictClusters.2 ⟨A, hA1, ?_, rfl⟩, ?_, hA3⟩
      · rw [← subtype_nonempty_iff]
        rcases hA3 with h | h <;> rw [h] <;> assumption
      · rcases hA3 with h | h <;> rw [h] <;> assumption
  -- the sum on the right side is `2 * M`: each cluster `A` is counted once as `A` and once as `Aᶜ`
  set f : Len X := fun B => if B ∈ σ.clusters ∧ B ≠ univ then σ.length B else 0 with hf
  have key1 : ∀ A, σ.unrootedLength A = f A + f Aᶜ := by
    intro A
    unfold unrootedLength
    rw [show σ.clusters.filter (fun B => B ≠ univ ∧ (B = A ∨ B = Aᶜ)) =
        ({A, Aᶜ} : Fam X).filter (fun B => B ∈ σ.clusters ∧ B ≠ univ) by
      ext B
      simp only [mem_filter, mem_insert, mem_singleton]
      tauto]
    rw [sum_filter, sum_pair ne_compl_self]
  have hT : ∀ A ∈ (unroot σ.clusters).filter p, Aᶜ ∈ (unroot σ.clusters).filter p := by
    intro A hA
    obtain ⟨hA1, hA2⟩ := mem_filter.1 hA
    exact mem_filter.2 ⟨compl_mem_unroot.2 hA1, (hpc A).2 hA2⟩
  have key2 : ∑ A ∈ (unroot σ.clusters).filter p, f Aᶜ =
      ∑ A ∈ (unroot σ.clusters).filter p, f A :=
    Finset.sum_nbij' compl compl hT hT (fun A _ => compl_compl A) (fun A _ => compl_compl A)
      (fun _ _ => rfl)
  have key3 : ∑ A ∈ (unroot σ.clusters).filter p, f A = M := by
    simp only [hf, hM]
    rw [← sum_filter, filter_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext A
    simp only [mem_filter]
    constructor
    · rintro ⟨-, hpA, hA, hAu⟩
      exact ⟨hA, hAu, hpA⟩
    · rintro ⟨hA, hAu, hpA⟩
      exact ⟨mem_unroot.2 (Or.inl ⟨hA, hAu⟩), hpA, hA, hAu⟩
  have hR : ∑ A ∈ unroot σ.clusters with p A, σ.unrootedLength A = 2 * M := by
    rw [Finset.sum_congr rfl fun A _ => key1 A, sum_add_distrib, key2, key3]
    ring
  rw [hL, hR]
  ring

/-- The two sides of a split have the same unrooted length. -/
theorem unrootedLength_compl (σ : SpeciesTree X) (A : Finset X) :
    σ.unrootedLength Aᶜ = σ.unrootedLength A := by
  unfold unrootedLength
  refine Finset.sum_congr (filter_congr fun B _ => ?_) fun _ _ => rfl
  rw [compl_compl, or_comm]

end SpeciesTree

end ADR11
