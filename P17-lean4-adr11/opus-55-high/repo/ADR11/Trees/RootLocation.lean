module

public import ADR11.External.Quartets.Steel

/-!
# The root of a species tree on its unrooted tree

Helpers for the paper's proof of Theorem 9 and of its extension to nonbinary species trees
(Proposition 11): locating the root `ρ` of a rooted species tree `σ⁺` on its unrooted tree `σ⁻`,
and recovering `σ⁺` from `σ⁻`, the location of the root, and induced five-taxon trees.

In the representation by clusters, the location of the root is given by the children of the root
(`childClusters σ.clusters univ`). The root lies on the edge `A | Aᶜ` of `σ⁻` (a root of degree
two) exactly when `A` and `Aᶜ` are clusters, and these are then the two children of the root. A
root of degree at least three is a vertex of `σ⁻`, at which the edges `R | Rᶜ` of the children `R`
of the root meet.

## Main results

* `rl_childClusters_univ_eq_pair`, `rl_eq_or_eq_compl`: two complementary clusters are the two
  children of the root, so a hierarchy has at most one pair of complementary clusters.
* `rl_exists_compl_mem`: the root of a binary species tree lies on an edge of `σ⁻`.
* `rl_mem_iff`, `rl_eq_of_unroot_eq`: the clusters other than the root are the sides of the splits
  of `σ⁻` contained in a child of the root, so a hierarchy is determined by its unrooted tree and
  the children of its root (it is the rooting of `σ⁻` at the location of the root).
* `rl_restrict_compl_mem`: if the root lies on the edge `A | Aᶜ` and `S` meets `A` and `Aᶜ`, the
  root of the induced tree `σ(S)` lies on the induced edge.
* `rl_mem_childClusters_restrict_iff`: if the most recent common ancestor of `S` is the root (`S`
  lies in no child of the root), the children of the root of `σ(S)` are the traces on `S` of the
  children of the root of `σ`.
* `rl_exists_five`: completing a set of taxa to a set of five taxa.
* `rl_sameRootedMetricTree_of_clusters_eq`: the last step of the proof of Theorem 9. Two species
  trees with the same clusters, the same unrooted metric tree and the same induced metric trees on
  five taxa have the same metric tree: the length of an edge not at a root of degree two is the
  length of its split in `σ⁻` (`rl_unrootedLength_eq_length`), and the length of an edge at a
  root of degree two is read off an induced tree `σ(S)` on five taxa that has this edge.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### The children of the root -/

/-- The complement of a set other than `univ` is nonempty. -/
theorem rl_compl_nonempty {A : Finset X} (hAu : A ≠ univ) : Aᶜ.Nonempty := by
  obtain ⟨x, hx⟩ := not_forall.1 fun h => hAu (eq_univ_iff_forall.2 h)
  exact ⟨x, mem_compl.2 hx⟩

/-- Two complementary clusters `A`, `Aᶜ` of a hierarchy are the children of its root. -/
theorem rl_childClusters_univ_eq_pair {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A : Finset X} (hA : A ∈ H) (hAc : Aᶜ ∈ H) : childClusters H univ = {A, Aᶜ} :=
  hH.childClusters_eq_pair hA hAc disjoint_compl_right (union_compl A)

/-- Every taxon lies in a child of the root (on at least two taxa). -/
theorem rl_exists_mem_childClusters_univ {H : Finset (Finset X)} (hH : IsHierarchy H)
    (hX : 2 ≤ Fintype.card X) (x : X) : ∃ R ∈ childClusters H univ, x ∈ R :=
  hH.exists_mem_childClusters (by rwa [card_univ]) (mem_univ x)

/-- Two children of the root with a common taxon are equal. -/
theorem rl_eq_of_mem_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {R R' : Finset X} (hR : R ∈ childClusters H univ) (hR' : R' ∈ childClusters H univ) {x : X}
    (hx : x ∈ R) (hx' : x ∈ R') : R = R' := by
  by_contra hne
  exact disjoint_left.1 (hH.disjoint_of_mem_childClusters hR hR' hne) hx hx'

/-- A child of the root is a cluster other than the root. -/
theorem rl_ne_univ_of_mem_childClusters {H : Finset (Finset X)} {R : Finset X}
    (hR : R ∈ childClusters H univ) : R ≠ univ :=
  ssubset_univ_iff.1 (mem_childClusters.1 hR).2.1

/-! ### Rooting the unrooted tree at the location of the root -/

/-- In a hierarchy, a side of a split contained in a cluster `A ≠ univ` is a cluster. -/
theorem counts_mem_of_mem_unroot_of_subset {G : Finset (Finset X)} (hG : IsHierarchy G)
    {A C : Finset X} (hA : A ∈ G) (hAu : A ≠ univ) (hC : C ∈ unroot G) (hCA : C ⊆ A) :
    C ∈ G := by
  rcases mem_unroot.1 hC with ⟨h, -⟩ | ⟨h, hu⟩
  · grind
  · rcases hG.2.2.2 _ h A hA with h' | h' | h'
    · exfalso
      refine hAu (eq_univ_iff_forall.2 fun x => ?_)
      by_contra hx
      exact hx (h' (compl_subset_compl.2 hCA (mem_compl.2 hx)))
    · exfalso
      refine hu (eq_univ_iff_forall.2 fun x => ?_)
      rw [mem_compl]
      intro hx
      exact mem_compl.1 (h' (hCA hx)) hx
    · have : Cᶜ = Aᶜ := Subset.antisymm (subset_compl_iff_disjoint_right.2 h')
        (compl_subset_compl.2 hCA)
      rwa [compl_inj_iff.1 this]

/-- The clusters of a hierarchy other than the root are the sides of the splits of its unrooted
tree that are contained in a child of the root. -/
theorem rl_mem_iff {H : Finset (Finset X)} (hH : IsHierarchy H) {C : Finset X} :
    C ∈ H ↔ C = univ ∨ (C ∈ unroot H ∧ ∃ R ∈ childClusters H univ, C ⊆ R) := by
  constructor
  · intro hC
    by_cases hCu : C = univ
    · grind
    · exact Or.inr ⟨mem_unroot.2 (Or.inl ⟨hC, hCu⟩),
        hH.exists_mem_childClusters_superset hC (ssubset_univ_iff.2 hCu)⟩
  · rintro (rfl | ⟨hC, R, hR, hCR⟩)
    · exact hH.1
    · exact counts_mem_of_mem_unroot_of_subset hH (mem_childClusters.1 hR).1
        (rl_ne_univ_of_mem_childClusters hR) hC hCR

/-- A hierarchy is determined by its unrooted tree and the children of its root: it is the
rooting of its unrooted tree at the location of the root. -/
theorem rl_eq_of_unroot_eq {H H' : Finset (Finset X)} (hH : IsHierarchy H)
    (hH' : IsHierarchy H') (hU : unroot H = unroot H')
    (hR : childClusters H univ = childClusters H' univ) : H = H' := by
  ext C
  rw [rl_mem_iff hH, rl_mem_iff hH', hU, hR]

/-! ### The root of an induced subtree -/

/-- If `S` lies in no child of the root of `σ` (the most recent common ancestor of `S` is the
root), the children of the root of the induced tree `σ(S)` are the traces on `S` of the children
of the root of `σ` that meet `S`. -/
theorem rl_mem_childClusters_restrict_iff (σ : SpeciesTree X) {S R₀ : Finset X} (hS : S.Nonempty)
    (hR₀ : R₀ ∈ childClusters σ.clusters univ) (h1 : (R₀ ∩ S).Nonempty)
    (h2 : (R₀ᶜ ∩ S).Nonempty) {C : Finset S} :
    C ∈ childClusters (σ.restrict S hS).clusters univ ↔
      ∃ R ∈ childClusters σ.clusters univ, (R ∩ S).Nonempty ∧ R.subtype (· ∈ S) = C := by
  have hH := σ.isHierarchy
  have hmrca : ∀ R ∈ childClusters σ.clusters univ, ¬ S ⊆ R := fun R hR hSR => by
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := And.intro h1 h2
    rw [mem_inter] at hx hy
    exact mem_compl.1 hy.1 (rl_eq_of_mem_childClusters hH hR₀ hR hx.1 (hSR hx.2) ▸ hSR hy.2)
  -- the trace of a child of the root that meets `S` is a cluster of `σ(S)` other than its root
  have htr : ∀ R ∈ childClusters σ.clusters univ, (R ∩ S).Nonempty →
      R.subtype (· ∈ S) ∈ (σ.restrict S hS).clusters ∧ R.subtype (· ∈ S) ⊂ univ := by
    intro R hR hRS
    refine ⟨subtype_mem_restrictClusters (mem_childClusters.1 hR).1 hRS,
      ssubset_univ_iff.2 (subtype_ne_univ_iff.2 ?_)⟩
    obtain ⟨y, hyS, hyR⟩ := not_subset.1 (hmrca R hR)
    exact ⟨y, mem_inter.2 ⟨mem_compl.2 hyR, hyS⟩⟩
  -- a cluster of `σ` other than the root lies in a child of the root
  have hsup : ∀ B ∈ σ.clusters, B ≠ univ → ∃ R ∈ childClusters σ.clusters univ, B ⊆ R :=
    fun B hB hBu => hH.exists_mem_childClusters_superset hB (ssubset_univ_iff.2 hBu)
  constructor
  · intro hC
    obtain ⟨hCcl, hCu, hmax⟩ := mem_childClusters.1 hC
    obtain ⟨B, hB, hBS, rfl⟩ := mem_restrictClusters.1 hCcl
    have hBu : B ≠ univ := by grind
    obtain ⟨R, hR, hBR⟩ := hsup B hB hBu
    have hRS : (R ∩ S).Nonempty := by
      obtain ⟨y, hy⟩ := hBS
      exact ⟨y, mem_inter.2 ⟨hBR (mem_inter.1 hy).1, (mem_inter.1 hy).2⟩⟩
    refine ⟨R, hR, hRS, ?_⟩
    obtain ⟨hRcl, hRu⟩ := htr R hR hRS
    rcases (subtype_mono hBR : B.subtype (· ∈ S) ⊆ R.subtype (· ∈ S)).eq_or_ssubset with h | h <;> grind
  · rintro ⟨R, hR, hRS, rfl⟩
    obtain ⟨hRcl, hRu⟩ := htr R hR hRS
    refine mem_childClusters.2 ⟨hRcl, hRu, fun D hD hRD hDu => ?_⟩
    obtain ⟨B, hB, -, rfl⟩ := mem_restrictClusters.1 hD
    have hBu : B ≠ univ := by grind
    -- `B` lies in a child of the root, which shares with `R` a taxon of `R ∩ S`, so `B ⊆ R`
    obtain ⟨R', hR', hBR'⟩ := hsup B hB hBu
    obtain ⟨y, hy⟩ := hRS
    have hyB := mem_subtype.1
      (hRD.subset (mem_subtype.2 (mem_inter.1 hy).1 : (⟨y, (mem_inter.1 hy).2⟩ : S) ∈ _))
    have := rl_eq_of_mem_childClusters hH hR hR' (mem_inter.1 hy).1 (hBR' hyB)
    subst this
    grind

/-! ### Sets of five taxa -/

/-- A set of at most five taxa is contained in a set of exactly five taxa. -/
theorem rl_exists_five (hX : 5 ≤ Fintype.card X) {T : Finset X} (hT : #T ≤ 5) :
    ∃ S, T ⊆ S ∧ #S = 5 := by
  obtain ⟨S, hTS, -, hS⟩ := exists_subsuperset_card_eq (subset_univ T) hT (by rwa [card_univ])
  grind

/-! ### Edge lengths -/

/-- The unrooted length of the split `A | Aᶜ` of a cluster `A ≠ univ` whose complement is not a
cluster (an edge not at a root of degree two) is the length of the edge above `A`. -/
theorem rl_unrootedLength_eq_length (σ : SpeciesTree X) {A : Finset X} (hA : A ∈ σ.clusters)
    (hAu : A ≠ univ) (hAc : Aᶜ ∉ σ.clusters) : σ.unrootedLength A = σ.length A := by
  unfold SpeciesTree.unrootedLength
  rw [Finset.sum_eq_single_of_mem A (mem_filter.2 ⟨hA, hAu, Or.inl rfl⟩)]
  intro C hC hCA
  obtain ⟨hC1, -, hC3⟩ := mem_filter.1 hC
  rcases hC3 with rfl | rfl <;> grind

/-- The edge lengths (last step of the proof of Theorem 9). Two species trees on at least five
taxa with the same clusters, the same unrooted metric tree, and the same induced metric trees on
all sets of five taxa have the same metric tree. The length of an edge not at a root of degree
two is the length of its split in `σ⁻`. At a root of degree two, with children `A` and `Aᶜ`, the
edge above `A` is the edge above `A ∩ S` in `σ(S)`, for a set `S` of five taxa containing two
taxa `a₁, a₂` in different children of `A` and a taxon `w ∉ A`. -/
theorem rl_sameRootedMetricTree_of_clusters_eq (hX : 5 ≤ Fintype.card X) {σ σ' : SpeciesTree X}
    (hcl : σ.clusters = σ'.clusters) (hU : σ.SameUnrootedMetricTree σ')
    (h5 : ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
      (σ.restrict S hS).SameRootedMetricTree (σ'.restrict S hS)) :
    σ.SameRootedMetricTree σ' := by
  refine ⟨hcl, fun A hA hA2 hAu => ?_⟩
  have hH := σ.isHierarchy
  by_cases hAc : Aᶜ ∈ σ.clusters
  · -- an edge at a root of degree two
    have hAR :=
      rl_childClusters_univ_eq_pair hH hA hAc ▸ mem_insert_self _ _
    obtain ⟨B₁, hB₁, B₂, hB₂, hne⟩ := one_lt_card.1 (hH.two_le_card_childClusters hA2)
    obtain ⟨a₁, ha₁⟩ := hH.2.2.1 B₁ (mem_childClusters.1 hB₁).1
    obtain ⟨a₂, ha₂⟩ := hH.2.2.1 B₂ (mem_childClusters.1 hB₂).1
    have hA₁ := (mem_childClusters.1 hB₁).2.1.subset ha₁
    obtain ⟨w, hw⟩ := hH.2.2.1 _ hAc
    obtain ⟨S, hTS, hS5⟩ := rl_exists_five hX (T := {a₁, a₂, w}) (card_le_three.trans (by norm_num))
    have hS : S.Nonempty := ⟨w, hTS (by simp)⟩
    -- `A` is the only cluster of `σ` (and of `σ'`) whose trace on `S` is `A ∩ S`
    have huniq : ∀ C ∈ σ.clusters, C.subtype (· ∈ S) = A.subtype (· ∈ S) → C = A := by
      intro C hC hCA
      have hmem : ∀ x ∈ ({a₁, a₂, w} : Finset X), x ∈ C ↔ x ∈ A :=
        fun x hx => mem_iff_of_subtype_eq hCA (hTS hx)
      refine Subset.antisymm ?_ ((hH.lca_pair_eq_of_mem_childClusters hA hB₁ hB₂ hne ha₁ ha₂) ▸ lca_subset hC (by
        simp [insert_subset_iff, (hmem a₁ (by simp)).2 hA₁,
          (hmem a₂ (by simp)).2 ((mem_childClusters.1 hB₂).2.1.subset ha₂)]))
      rcases σ.laminar C hC _ hAc with h | h | h
      · exact absurd (h ((hmem a₁ (by simp)).2 hA₁)) (by simpa using hA₁)
      · exact absurd ((hmem w (by simp)).1 (h hw)) (mem_compl.1 hw)
      · exact fun x hx => by simpa using disjoint_left.1 h hx
    have := (h5 S hS hS5).2 _ (subtype_mem_restrictClusters hA ⟨a₁, mem_inter.2 ⟨hA₁, hTS (by simp)⟩⟩)
      (one_lt_card.2 ⟨⟨a₁, hTS (by simp)⟩, by simp [hA₁], ⟨a₂, hTS (by simp)⟩,
        by simp [(mem_childClusters.1 hB₂).2.1.subset ha₂], fun h => disjoint_left.1
          (hH.disjoint_of_mem_childClusters hB₁ hB₂ hne) ha₁ (by simp_all)⟩)
      (subtype_ne_univ_iff.2 ⟨w, mem_inter.2 ⟨hw, hTS (by simp)⟩⟩)
    rwa [SpeciesTree.restrict_length, SpeciesTree.restrict_length,
      σ.restrictLength_subtype_eq hA hAu huniq,
      σ'.restrictLength_subtype_eq (hcl ▸ hA) hAu fun C hC => huniq C (hcl ▸ hC)] at this
  · -- an edge not at the root: its length is the length of its split in `σ⁻`
    have hAc2 : 2 ≤ #Aᶜ := by
      by_contra hlt
      obtain ⟨x, hx⟩ := card_eq_one.1
        (le_antisymm (by omega) (card_pos.2 (rl_compl_nonempty hAu)))
      exact hAc (hx ▸ σ.singleton_mem x)
    have hAc' : Aᶜ ∉ σ'.clusters := by grind
    rw [← rl_unrootedLength_eq_length σ hA hAu hAc,
      ← rl_unrootedLength_eq_length σ' (hcl ▸ hA) hAu hAc']
    exact hU.2 A (mem_unroot.2 (Or.inl ⟨hA, hAu⟩)) hA2 hAc2

end ADR11
