module

public import ADR11.Identifiability.RootedFive
public import ADR11.Identifiability.FourTaxaAnalysis
public import ADR11.Trees.RootLocation
public import ADR11.MSC.Marginal
public import ADR11.Identifiability.FiveQuartets
@[expose] public section
namespace ADR11
open Finset
variable {X : Type*} [Fintype X] [DecidableEq X] {L : Type*} [Fintype L] [DecidableEq L]
variable (σ : SpeciesTree X)
variable {H : Family X} {A : Finset X} {s : L → X}

/-- The clusters of the extended species tree. -/
def extendClusters (H : Family X) (s : L → X) : Family L :=
  H.image (fun A => clusterPreimage s A) ∪ univ.image fun l => {l}

/-! ### Preimages of clusters under the sampling map -/

private lemma multi_mem_extendClusters (s : L → X)
    (hA : A ∈ H) : (clusterPreimage s A) ∈ extendClusters H s :=
  mem_union_left _ (mem_image_of_mem _ hA)

private lemma multi_pre_univ (s : L → X) :
    (clusterPreimage s (univ : Finset X)) = univ :=
  filter_true_of_mem fun _ _ => mem_univ _

/-- A set of taxa whose preimage is a singleton `{l}` is the singleton `{s l}`. -/
private lemma multi_sampledForest_pre (s : L → X) (A : Finset X) :
    sampledForest s A = sampledForest id (clusterPreimage s A) := by
  simp [sampledForest]

variable (hs : Function.Surjective s)
include hs

private lemma multi_image_pre (A : Finset X) :
    (clusterPreimage s A).image s = A := by
  rw [clusterPreimage, ← filter_image (p := (· ∈ A)), image_univ_of_surjective hs]
  simp

private abbrev preEmb : Finset X ↪o Finset L :=
  OrderEmbedding.ofMapLEIff (clusterPreimage s) fun A B => by
    refine ⟨fun h => ?_, clusterPreimage_mono s⟩
    simpa only [multi_image_pre hs] using image_subset_image (f := s) h

private lemma multi_pre_ne_univ (hA : A ≠ univ) : (clusterPreimage s A) ≠ univ :=
  fun h => hA ((preEmb hs).injective (h.trans (multi_pre_univ s).symm))

/-! ### The extended species tree -/

/-- The lengths of the extended species tree: a cluster `s⁻¹(A)` keeps the length of `A`; a new
singleton cluster gets length `1`. -/
def SpeciesTree.extendLength (s : L → X) (B : Finset L) : ℝ :=
  if B.image s ∈ σ.clusters ∧ B.image s ≠ univ then σ.length (B.image s) else 1

/-- The extended species tree on the lineages `L`. -/
def SpeciesTree.extend (s : L → X)
    (hs : Function.Surjective s) : SpeciesTree L where
  clusters := extendClusters σ.clusters s
  univ_mem := by
    rw [← multi_pre_univ s]
    exact multi_mem_extendClusters s σ.univ_mem
  singleton_mem := fun l => mem_union_right _ (mem_image_of_mem _ (mem_univ l))
  nonempty_of_mem := by
    simp only [extendClusters, forall_mem_union, forall_mem_image,
      ← Finset.image_nonempty (f := s), multi_image_pre hs, image_singleton, singleton_nonempty]
    simpa using σ.nonempty_of_mem
  laminar := by
    have := σ.laminar
    grind [extendClusters, clusterPreimage_mono s, disjoint_left]
  length := σ.extendLength s
  length_pos := by
    intro B _ _
    unfold SpeciesTree.extendLength
    split_ifs <;> simp_all [σ.length_pos]

/-- The edge above the preimage of a cluster with at least two lineages keeps its length. -/
private lemma multi_extendLength_pre
    (hA : A ∈ σ.clusters) (hAu : A ≠ univ) :
    σ.extendLength s (clusterPreimage s A) = σ.length A := by
  simp_all [SpeciesTree.extendLength, multi_image_pre hs]

/-- The population above the preimage of a cluster with at least two lineages is the population
above the cluster. -/
private lemma multi_populationKernel_pre
    (hA : A ∈ σ.clusters) :
    populationKernel (L := L) σ.length A =
      populationKernel (σ.extendLength s) (clusterPreimage s A) := by
  by_cases hAu : A = univ <;>
    simp_all [populationKernel, multi_pre_univ, multi_pre_ne_univ hs,
      multi_extendLength_pre σ hs]

/-- The children of the preimage of a cluster with at least two taxa are the preimages of its
children. -/
private lemma multi_childClusters_pre
    (h2 : 2 ≤ #A) :
    childClusters (extendClusters σ.clusters s) (clusterPreimage s A) =
      (childClusters σ.clusters A).image fun B => clusterPreimage s B := by
  unfold extendClusters
  rw [childClusters_union_eq]
  · exact childClusters_image (preEmb hs) _ _
  · intro B hB hBA
    obtain ⟨l, -, rfl⟩ := mem_image.1 hB
    obtain ⟨C, hC, hlC⟩ := σ.isHierarchy.exists_mem_childClusters h2 (by simpa using hBA.subset (mem_singleton_self l))
    exact ⟨clusterPreimage s C, mem_image_of_mem _ (mem_childClusters.1 hC).1,
      by simpa using hlC,
      (preEmb hs).lt_iff_lt.2 (mem_childClusters.1 hC).2.1⟩

/-- The multispecies coalescent below a cluster `A` with at most two lineages per taxon is the
multispecies coalescent below `s⁻¹(A)` in the extended species tree, with one lineage per leaf. -/
private lemma multi_forestDist_extend
    (hA : A ∈ σ.clusters) (G : Family L) :
    forestDist σ.clusters σ.length s A G =
      forestDist (extendClusters σ.clusters s) (σ.extendLength s) id
        (clusterPreimage s A) G := by
  have hE : IsHierarchy (extendClusters σ.clusters s) := (σ.extend s hs).isHierarchy
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  obtain ⟨x, hx⟩ := σ.nonempty_of_mem A hA
  rcases Nat.lt_or_ge 1 #A with hA2 | hA1
  · -- an internal node: the children of `s⁻¹(A)` are the preimages of the children of `A`
    let e : childClusters σ.clusters A ≃
        childClusters (extendClusters σ.clusters s) (clusterPreimage s A) :=
      (Finset.equivMap (preEmb hs).toEmbedding _).trans
        (Finset.equivOfEq ((Finset.map_eq_image _ _).trans (multi_childClusters_pre σ hs (show 2 ≤ #A from hA2)).symm))
    rw [forestDist.eq_1 σ.clusters σ.length, forestDist.eq_1 (extendClusters σ.clusters s),
      ← (e.arrowCongr (Equiv.refl (Family L))).sum_comp]
    refine Finset.sum_congr rfl fun g _ => ?_
    congr 1
    · refine Fintype.prod_equiv e _ _ fun B => ?_
      simpa [Equiv.arrowCongr_apply, e] using
        ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1 (g B)
    · rw [multi_populationKernel_pre σ hs hA, multi_sampledForest_pre s A]
      congr 2
      exact (sup_univ_equiv e.symm g).symm
  · -- a leaf `{x}` from which one or two lineages are sampled
    have hAx : A = {x} := by grind [card_le_one]
    subst hAx
    rw [forestDist_of_childClusters_eq_empty (σ.isHierarchy.childClusters_singleton x),
      multi_populationKernel_pre σ hs hA,
      multi_sampledForest_pre s {x}]
    symm
    have hFD : ∀ (B : childClusters (extendClusters σ.clusters s)
        (clusterPreimage s {x})) F,
        forestDist (extendClusters σ.clusters s) (σ.extendLength s) id B F =
          if F = sampledForest id B then 1 else 0 := by
      intro B F
      rcases mem_union.1 (mem_childClusters.1 B.2).1 with h | h
      · obtain ⟨C, hC, hCB⟩ := mem_image.1 h
        have : C = ∅ := ssubset_singleton_iff.1
          ((preEmb hs).lt_iff_lt.1 (hCB ▸ (mem_childClusters.1 B.2).2.1))
        exact ((σ.nonempty_of_mem C hC).ne_empty this).elim
      · obtain ⟨l, _, hBl⟩ := mem_image.1 h
        rw [← hBl, forestDist_id_singleton hE]
    rw [forestDist]
    simp_rw [hFD, Fintype.prod_ite_zero, prod_const_one, ← funext_iff, ite_mul, one_mul, zero_mul]
    rw [sum_ite_eq']
    simp
    congr 2
    apply union_eq_right.2
    apply Finset.sup_le
    intro B _
    grind [mem_sampledForest, mem_childClusters]

/-- With at most two lineages per taxon, sampling through `s` is sampling one lineage per leaf of
the extended species tree. -/
theorem SpeciesTree.rootedDist_extend
    (G : Family L) :
    σ.rootedDist s G = (σ.extend s hs).rootedDist id G := by
  unfold SpeciesTree.rootedDist
  rw [multi_forestDist_extend σ hs σ.univ_mem G, multi_pre_univ]
  rfl

omit hs
set_option maxHeartbeats 0

/-- **Proposition 11** (`prop:nonbinary`), Theorem 9 for nonbinary species trees, `|X| ≥ 5`.

Departure from the paper: as in `theorem9`, no quartet distinguishes a pendant edge, so for a
pendant edge the five-taxon set that locates the root is chosen differently
(`rl_nb_theorem9`, audit item E4). -/
theorem proposition11_theorem9 (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameRootedMetricTree σ' :=
  same_of_fives hX fun S hS hS5 => by
    let τ := σ.restrict S hS
    let τ' := σ'.restrict S hS
    have h := unrootedDist_restrict_eq h S hS
    obtain ⟨e, k, he⟩ := Shape.normal (Or.inr rfl) (by simpa using hS5) U5 3 (by decide +kernel) τ
    have hd := (SpeciesTree.unrootedDist_relabel_eq_iff τ τ' e.symm).2 h
    have hU := FiveQuartet.same_of_restrict _ _ fun Q hQ hQ4 =>
      (unrootedDist_eq_iff_four (by simpa using hQ4) _ _).1 (unrootedDist_restrict_eq hd Q hQ)
    apply (SpeciesTree.sameRootedMetricTree_relabel_iff τ τ' e.symm).1
    exact Five.same k _ _ he (hU.1 ▸ he) hU hd

/-- **Proposition 11** (`prop:nonbinary`), Corollary 10 for nonbinary species trees. -/
theorem proposition11_corollary10 (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist (@Sigma.fst X (fun x => Fin (ℓ x))) =
      σ'.unrootedDist (@Sigma.fst X (fun x => Fin (ℓ x)))) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} := by
  let s : (Σ x, Fin (ℓ x)) → X := Sigma.fst
  have hsurj : Function.Surjective s := fun x => ⟨⟨x, ⟨0, hℓ x⟩⟩, rfl⟩
  -- The extended species trees: the coalescent with one lineage per leaf of the extended tree
  -- gives the same gene tree distribution as the multiple-sample process on the species tree.
  -- Applying Theorem 9 to the extended trees, we obtain the result.
  have h5 : 5 ≤ Fintype.card (Σ x, Fin (ℓ x)) := by
    rw [Fintype.card_sigma]
    simp_all
    rcases hcond with ⟨h4,x,hx⟩ | ⟨h3,x,y,hxy,hx,hy⟩
    · have hs := sum_lt_sum (s := univ) (f := fun _ => 1) (fun z _ => hℓ z)
        ⟨x, mem_univ x, hx⟩
      simp at hs
      omega
    · have hs := sum_lt_sum (s := univ.erase x) (f := fun _ => 1) (fun z _ => hℓ z)
        ⟨y, by simp [Ne.symm hxy], hy⟩
      simp at hs
      have := sum_erase_add univ ℓ (mem_univ x)
      omega
  have hX : 2 ≤ Fintype.card X := by omega
  obtain ⟨hcl, hlen⟩ := proposition11_theorem9 h5 (σ.extend s hsurj) (σ'.extend s hsurj) (by
    funext T
    simpa only [SpeciesTree.unrootedDist, ← σ.rootedDist_extend hsurj,
      ← σ'.rootedDist_extend hsurj] using congrFun h T)
  change extendClusters σ.clusters s = extendClusters σ'.clusters s at hcl
  have hcl' : σ.clusters = σ'.clusters := by
    simpa [extendClusters, image_union, image_image, Function.comp_def, multi_image_pre hsurj,
      image_subset_iff, union_eq_left.mpr, σ.singleton_mem, σ'.singleton_mem] using congrArg (image (image s)) hcl
  have key : ∀ A ∈ σ.clusters, 2 ≤ #(clusterPreimage s A) → A ≠ univ →
      σ.length A = σ'.length A := by
    intro A hA h2 hAu
    have := hlen _ (multi_mem_extendClusters s hA) h2 (multi_pre_ne_univ hsurj hAu)
    change σ.extendLength s _ = σ'.extendLength s _ at this
    rwa [multi_extendLength_pre σ hsurj hA hAu, multi_extendLength_pre σ' hsurj (hcl' ▸ hA) hAu] at this
  refine ⟨⟨hcl', fun A hA hA2 hAu => key A hA (hA2.trans (by simpa only [multi_image_pre hsurj] using
      (card_image_le (s := clusterPreimage s A) (f := s)))) hAu⟩,
    fun x hx => key {x} (σ.singleton_mem x) (by
      rw [clusterPreimage, card_filter, Fintype.sum_sigma]
      simpa [s, apply_ite] using hx) (by simpa only [← card_lt_iff_ne_univ, card_singleton, Nat.succ_le_iff] using hX)⟩

end ADR11
