module

public import ADR11.MSC.Basic

/-!
# Combinatorics of rooted species trees (hierarchies)

## Main results

* `IsHierarchy.mem_of_triples`: a nonempty set `A` is a cluster as soon as, for all `a, a' ∈ A`
  and `b ∉ A`, some cluster contains `a` and `a'` but not `b` (rooted triples determine a rooted
  tree).
* `SpeciesTree.restrict_isBinary`: the induced subtree of a binary species tree is binary.
* `SpeciesTree.sameUnrootedMetricTree_of_card_le_three`: on at most three taxa all unrooted metric
  species trees agree (there is no internal edge).
* `SpeciesTree.restrict_unroot`, `SpeciesTree.restrict_unrootedLength`: induced subtrees and
  unrooting commute, and the unrooted length of a split of `σ(S)` is the sum of the unrooted
  lengths of the splits of `σ` that induce it.

## General facts on hierarchies

(The children of a cluster are also treated in `ADR11.MSC.Basic`: `mem_childClusters`,
`IsHierarchy.disjoint_of_mem_childClusters`, `IsHierarchy.exists_mem_childClusters`,
`IsHierarchy.two_le_card_childClusters`, `IsHierarchy.childClusters_eq_pair`.)

* `IsHierarchy.subset_or_subset_of_mem`: clusters with a common element are nested.
* `lca H T`: the smallest cluster containing `T`; `IsHierarchy.lca_mem`, `subset_lca`,
  `lca_subset`, `IsHierarchy.lca_eq_iff`, `IsHierarchy.lca_pair_eq_of_mem_childClusters`.
* `IsHierarchy.subset_of_mem_childClusters`, `IsHierarchy.existsUnique_mem_childClusters`,
  `IsHierarchy.exists_mem_childClusters_superset`: the children of a cluster partition it, and
  every cluster strictly inside it lies inside a child.
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

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Clusters with a common element are nested -/

namespace IsHierarchy

variable {H : Finset (Finset X)}

/-- Two clusters of a hierarchy with a common element are nested. -/
theorem subset_or_subset_of_mem (hH : IsHierarchy H) {A B : Finset X} (hA : A ∈ H) (hB : B ∈ H)
    {x : X} (hxA : x ∈ A) (hxB : x ∈ B) : A ⊆ B ∨ B ⊆ A := by
  grind [hH.2.2.2 A hA B hB, disjoint_left]

/-- Two clusters of a hierarchy that are not disjoint are nested. -/
theorem subset_or_subset_of_not_disjoint (hH : IsHierarchy H) {A B : Finset X} (hA : A ∈ H)
    (hB : B ∈ H) (hAB : ¬ Disjoint A B) : A ⊆ B ∨ B ⊆ A := by
  obtain ⟨x, hxA, hxB⟩ := not_disjoint_iff.1 hAB
  exact hH.subset_or_subset_of_mem hA hB hxA hxB

/-- The clusters of a hierarchy containing a common element `x` and satisfying `p` are closed
under union (the union of two of them is one of them). -/
theorem hier_sup_mem (hH : IsHierarchy H) (x : X) (p : Finset X → Prop) :
    ∀ C ∈ {C | C ∈ H ∧ x ∈ C ∧ p C}, ∀ D ∈ {C | C ∈ H ∧ x ∈ C ∧ p C},
      C ⊔ D ∈ {C | C ∈ H ∧ x ∈ C ∧ p C} := by
  rintro C hC D hD
  rcases hH.subset_or_subset_of_mem hC.1 hD.1 hC.2.1 hD.2.1 with h | h <;> simp_all

/-- The clusters of a hierarchy containing a common element `x` and satisfying `p` are closed
under intersection. -/
theorem hier_inf_mem (hH : IsHierarchy H) (x : X) (p : Finset X → Prop) :
    ∀ C ∈ {C | C ∈ H ∧ x ∈ C ∧ p C}, ∀ D ∈ {C | C ∈ H ∧ x ∈ C ∧ p C},
      C ⊓ D ∈ {C | C ∈ H ∧ x ∈ C ∧ p C} := by
  rintro C hC D hD
  rcases hH.subset_or_subset_of_mem hC.1 hD.1 hC.2.1 hD.2.1 with h | h <;> simp_all

end IsHierarchy

/-! ### The smallest cluster containing a set -/

/-- The smallest cluster of `H` containing `T`: the intersection of the clusters of `H` that
contain `T`. For a hierarchy `H` and a nonempty `T` it is a cluster of `H` (`IsHierarchy.lca_mem`),
the cluster of the most recent common ancestor of the taxa in `T`. -/
def lca (H : Finset (Finset X)) (T : Finset X) : Finset X :=
  (H.filter (T ⊆ ·)).inf id

/-- A set is contained in the smallest cluster containing it. -/
theorem subset_lca (H : Finset (Finset X)) (T : Finset X) : T ⊆ lca H T := by simp_all [lca]

/-- The smallest cluster containing `T` is contained in every cluster containing `T`. -/
theorem lca_subset {H : Finset (Finset X)} {T C : Finset X} (hC : C ∈ H) (hTC : T ⊆ C) :
    lca H T ⊆ C :=
  Finset.inf_le (f := id) (mem_filter.2 ⟨hC, hTC⟩)

namespace IsHierarchy

variable {H : Finset (Finset X)}

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

variable {H : Finset (Finset X)}

/-- A cluster strictly contained in `A` that meets a child `B` of `A` is contained in `B`. -/
theorem subset_of_mem_childClusters (hH : IsHierarchy H) {A B C : Finset X}
    (hB : B ∈ childClusters H A) (hC : C ∈ H) (hCA : C ⊂ A) (hBC : ¬ Disjoint B C) : C ⊆ B := by
  rw [mem_childClusters] at hB
  rcases hH.subset_or_subset_of_not_disjoint hB.1 hC hBC with h | h <;> grind

/-- Every element `x` of a cluster `A ≠ {x}` lies in a child of `A` (the cluster `A` need not be a
member of `H`). -/
theorem exists_mem_childClusters_of_ne (hH : IsHierarchy H) {A : Finset X} {x : X} (hx : x ∈ A)
    (hAx : A ≠ {x}) : ∃ B ∈ childClusters H A, x ∈ B := by
  set F := H.filter (fun C => x ∈ C ∧ C ⊂ A)
  have hF : F.Nonempty := ⟨{x}, mem_filter.2 ⟨hH.2.1 x, mem_singleton_self x,
    ssubset_of_subset_not_subset (singleton_subset_iff.2 hx)
      (fun h => hAx (Subset.antisymm h (singleton_subset_iff.2 hx)))⟩⟩
  have hmem :=
    Finset.sup'_mem _ (hier_sup_mem hH x (· ⊂ A)) F hF id (fun C hC => mem_filter.1 hC)
  refine ⟨F.sup' hF id, mem_childClusters.2 ⟨hmem.1, hmem.2.2, fun C hC hBC hCA => ?_⟩,
    hmem.2.1⟩
  have : C ⊆ F.sup' hF id :=
    Finset.le_sup' id (mem_filter.2 ⟨hC, hBC.subset hmem.2.1, hCA⟩)
  grind

/-- A cluster strictly contained in `A` is contained in a child of `A`. -/
theorem exists_mem_childClusters_superset (hH : IsHierarchy H) {A B : Finset X} (hB : B ∈ H)
    (hBA : B ⊂ A) : ∃ C ∈ childClusters H A, B ⊆ C := by
  obtain ⟨b, hb⟩ := hH.2.2.1 B hB
  have hAb : A ≠ {b} := by grind
  obtain ⟨C, hC, hbC⟩ := hH.exists_mem_childClusters_of_ne (hBA.subset hb) hAb
  exact ⟨C, hC, hH.subset_of_mem_childClusters hC hB hBA (not_disjoint_iff.2 ⟨b, hbC, hb⟩)⟩

/-- Two taxa in different children of a cluster `A` have `A` as their smallest common cluster. -/
theorem lca_pair_eq_of_mem_childClusters (hH : IsHierarchy H) {A B₁ B₂ : Finset X} (hA : A ∈ H)
    (hB₁ : B₁ ∈ childClusters H A) (hB₂ : B₂ ∈ childClusters H A) (hne : B₁ ≠ B₂) {a₁ a₂ : X}
    (ha₁ : a₁ ∈ B₁) (ha₂ : a₂ ∈ B₂) : lca H {a₁, a₂} = A := by
  have hA₁ := (mem_childClusters.1 hB₁).2.1.subset ha₁
  have hA₂ := (mem_childClusters.1 hB₂).2.1.subset ha₂
  refine (hH.lca_eq_iff (insert_nonempty a₁ {a₂})).2 ⟨hA, ?_, fun D hD hsub => ?_⟩
  · grind
  · rw [insert_subset_iff, singleton_subset_iff] at hsub
    rcases hH.subset_or_subset_of_mem hD hA hsub.1 hA₁ with h | h
    · by_contra hDA
      have hD' : D ⊂ A := by grind
      have h₁ := hH.subset_of_mem_childClusters hB₁ hD hD'
        (not_disjoint_iff.2 ⟨a₁, ha₁, hsub.1⟩)
      exact disjoint_left.1 (hH.disjoint_of_mem_childClusters hB₁ hB₂ hne) (h₁ hsub.2) ha₂
    · grind

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
theorem mem_restrictClusters {S : Finset X} {H : Finset (Finset X)} {C : Finset S} :
    C ∈ restrictClusters S H ↔ ∃ A ∈ H, (A ∩ S).Nonempty ∧ A.subtype (· ∈ S) = C := by
  unfold restrictClusters
  rw [mem_image]
  simp [mem_filter, and_assoc]

/-- The splits of the induced unrooted tree on `S` are the traces of the splits whose two sides
both meet `S`. -/
theorem mem_restrictSplits {S : Finset X} {T : Finset (Finset X)} {C : Finset S} :
    C ∈ restrictSplits S T ↔
      ∃ A ∈ T, (A ∩ S).Nonempty ∧ (Aᶜ ∩ S).Nonempty ∧ A.subtype (· ∈ S) = C := by
  unfold restrictSplits
  rw [mem_image]
  simp [mem_filter, and_assoc]

theorem subtype_nonempty_iff {S A : Finset X} :
    (A.subtype (· ∈ S)).Nonempty ↔ (A ∩ S).Nonempty := by
  simp [Finset.Nonempty, and_comm]

theorem mem_iff_of_subtype_eq {S A B : Finset X}
    (h : A.subtype (· ∈ S) = B.subtype (· ∈ S)) {x : X} (hx : x ∈ S) : x ∈ A ↔ x ∈ B := by
  simpa using congrArg (⟨x, hx⟩ ∈ ·) h

/-- The trace of the complement is the complement of the trace. -/
theorem subtype_compl {S : Finset X} (A : Finset X) :
    Aᶜ.subtype (· ∈ S) = (A.subtype (· ∈ S))ᶜ := by aesop

/-- The trace of `A` on `S` is not all of `S` if and only if `Aᶜ` meets `S`. -/
theorem subtype_ne_univ_iff {S A : Finset X} :
    A.subtype (· ∈ S) ≠ univ ↔ (Aᶜ ∩ S).Nonempty := by
  rw [← subtype_nonempty_iff, subtype_compl, Ne, ← compl_eq_empty_iff,
    ← not_nonempty_iff_eq_empty, not_not]

/-- The trace of a cluster meeting `S` is a cluster of the induced tree on `S`. -/
theorem subtype_mem_restrictClusters {S : Finset X} {H : Finset (Finset X)} {A : Finset X}
    (hA : A ∈ H) (hAS : (A ∩ S).Nonempty) : A.subtype (· ∈ S) ∈ restrictClusters S H :=
  mem_restrictClusters.2 ⟨A, hA, hAS, rfl⟩

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
  grind

end SpeciesTree

/-- The sides of the splits of the unrooted tree of a hierarchy are nonempty proper subsets. -/
theorem nonempty_of_mem_unroot {G : Finset (Finset X)} (hG : IsHierarchy G)
    {A : Finset X} (hA : A ∈ unroot G) : A.Nonempty ∧ A ≠ univ := by
  rcases mem_unroot.1 hA with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨hG.2.2.1 A h1, h2⟩
  · refine ⟨(compl_ne_univ_iff_nonempty A).1 h2, ?_⟩
    rintro rfl
    rw [compl_univ] at h1
    exact not_nonempty_empty (hG.2.2.1 _ h1)

/-! ### Rooted triples -/

/-- Rooted triples determine the clusters of a hierarchy: if for all `a, a' ∈ A` and `b ∉ A` some
cluster of `H` contains `a` and `a'` but not `b`, then `A` is a cluster of `H`. -/
theorem IsHierarchy.mem_of_triples {H : Finset (Finset X)} (hH : IsHierarchy H) {A : Finset X}
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
  have hU :=
    Finset.sup'_mem _ (IsHierarchy.hier_sup_mem hH a (b ∉ ·)) F hF id
      (fun C hC => mem_filter.1 hC)
  have hAU : A ⊆ F.sup' hF id := fun a' ha' => by
    obtain ⟨C, hC, haC, ha'C, hbC⟩ := h a ha a' ha' b hbA
    exact Finset.le_sup' id (mem_filter.2 ⟨hC, haC, hbC⟩) ha'C
  exact hU.2.2 (lca_subset hU.1 hAU hbL)

namespace SpeciesTree

/-! ### Induced subtrees of binary trees -/

/-! ### Agreement of metric trees -/

/-! ### Unrooting induced subtrees -/

/-- The unrooted topology of an induced subtree is the induced unrooted topology. -/
theorem restrict_unroot (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    unroot (σ.restrict S hS).clusters = restrictSplits S (unroot σ.clusters) := by
  ext C
  simp only [mem_unroot, restrict_clusters, mem_restrictSplits, mem_restrictClusters]
  constructor
  · rintro (⟨⟨A, hA, hAS, rfl⟩, hCu⟩ | ⟨⟨A, hA, hAS, hAC⟩, hCu⟩)
    · exact ⟨A, .inl ⟨hA, by rintro rfl; simp at hCu⟩, hAS, subtype_ne_univ_iff.1 hCu, rfl⟩
    · refine ⟨Aᶜ, .inr ⟨by rwa [compl_compl], by rw [compl_compl]; rintro rfl; exact hCu (hAC ▸ subtype_univ _)⟩,
        subtype_ne_univ_iff.1 (hAC ▸ hCu), by rwa [compl_compl], by rw [subtype_compl, hAC, compl_compl]⟩
  · rintro ⟨A, hA | hA, hAS, hAcS, rfl⟩
    · exact .inl ⟨⟨A, hA.1, hAS, rfl⟩, subtype_ne_univ_iff.2 hAcS⟩
    · exact .inr ⟨⟨Aᶜ, hA.1, hAcS, subtype_compl A⟩, by rw [← subtype_compl]; exact subtype_ne_univ_iff.2 (by rwa [compl_compl])⟩

/-- The length of an edge of the unrooted induced subtree `σ⁻(S)`: the sum of the lengths of the
edges above the clusters of `σ` whose trace is a side of its split. -/
theorem restrict_unrootedLength (σ : SpeciesTree X) {S : Finset X} (hS : S.Nonempty)
    {C : Finset S} (hC : C.Nonempty) (hCu : C ≠ univ) :
    (σ.restrict S hS).unrootedLength C = ∑ B ∈ σ.clusters with
      B ≠ univ ∧ (B.subtype (· ∈ S) = C ∨ B.subtype (· ∈ S) = Cᶜ), σ.length B := by
  have hCc : Cᶜ.Nonempty := by simpa [nonempty_iff_ne_empty] using hCu
  have hCcu := (compl_ne_univ_iff_nonempty C).2 hC
  unfold unrootedLength
  rw [restrict_clusters, restrict_length, eq_comm, ← sum_fiberwise_of_maps_to
    (g := fun B => B.subtype (· ∈ S))
    (t := (restrictClusters S σ.clusters).filter fun D => D ≠ univ ∧ (D = C ∨ D = Cᶜ))]
  · refine sum_congr rfl fun D hD => ?_
    rw [restrictLength, filter_filter]
    refine sum_congr (filter_congr fun B _ => ?_) fun _ _ => rfl
    grind
  · intro B hB
    simp only [mem_filter] at hB ⊢
    refine ⟨mem_restrictClusters.2 ⟨B, hB.1, subtype_nonempty_iff.1 ?_, rfl⟩, ?_, hB.2.2⟩ <;>
      rcases hB.2.2 with h | h <;> rw [h] <;> assumption

/-- The two sides of a split have the same unrooted length. -/
theorem unrootedLength_compl (σ : SpeciesTree X) (A : Finset X) :
    σ.unrootedLength Aᶜ = σ.unrootedLength A := by
  refine Finset.sum_congr (filter_congr fun B _ => ?_) fun _ _ => rfl
  rw [compl_compl, or_comm]

end SpeciesTree

end ADR11
