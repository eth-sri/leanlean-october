module

public import ADR11.MSC.Independent

/-! Sampling several lineages is equivalent to placing them at the leaves of an extended
species tree, in which each sampling fibre inherits its taxon's pendant length. -/

@[expose] public section

namespace ADR11
open Finset Independent
open scoped Independent
variable {X L : Type*} [Fintype L] [DecidableEq X]

theorem preLE {s : L → X} (hs : Function.Surjective s) (A B : Finset X) :
    samplesIn s A ⊆ samplesIn s B ↔ A ⊆ B := by
  simpa only [subset_iff, mem_samplesIn] using (hs.forall (p := fun x => x ∈ A → x ∈ B)).symm

private def preEmb {s : L → X} (hs : Function.Surjective s) : Finset X ↪o Finset L :=
  OrderEmbedding.ofMapLEIff (samplesIn s) (preLE hs)

@[local simp] theorem image_pre {s : L → X} (hs : Function.Surjective s) (A : Finset X) :
    (samplesIn s A).image s = A := by
  ext x
  have := hs x
  grind [mem_samplesIn]

private theorem card_pre {s : L → X} (hs : Function.Surjective s) (A : Finset X) : #A ≤ #(samplesIn s A) :=
  by simpa only [image_pre hs] using (card_image_le (s := samplesIn s A) (f := s))

theorem nonempty_pre {s : L → X} (hs : Function.Surjective s) {A : Finset X} (hA : A.Nonempty) :
    (samplesIn s A).Nonempty := card_pos.1 (hA.card_pos.trans_le (card_pre hs A))

variable [Fintype X] [DecidableEq L]

omit [DecidableEq L] in
@[local simp] theorem pre_univ (s : L → X) : samplesIn s univ = univ := by ext; simp

omit [DecidableEq L] in
private theorem pre_eq_top {s : L → X} (hs : Function.Surjective s) {A : Finset X} :
    samplesIn s A = univ ↔ A = univ := by
  rw [← pre_univ s]
  exact (preEmb hs).injective.eq_iff

def extendClusters (H : ClusterFamily X) (s : L → X) : ClusterFamily L :=
  H.image (samplesIn s) ∪ univ.image fun l => {l}

omit [Fintype X] in
theorem pre_mem {H : ClusterFamily X} (s : L → X) {A : Finset X} (hA : A ∈ H) :
    samplesIn s A ∈ extendClusters H s := mem_union_left _ (mem_image_of_mem _ hA)

omit [Fintype X] in
theorem extend_cases {H : ClusterFamily X} {s : L → X} {B : Finset L} :
    B ∈ extendClusters H s ↔ (∃ A ∈ H, samplesIn s A = B) ∨ ∃ l, {l} = B := by
  simp [extendClusters]

theorem image_extendClusters (σ : SpeciesTree X) {s : L → X} (hs : Function.Surjective s) :
    (extendClusters σ.clusters s).image (image s) = σ.clusters := by
  simp only [extendClusters, image_union, image_image, Function.comp_def, image_pre hs, image_id', image_singleton]
  exact union_eq_left.2 (image_subset_iff.2 fun l _ => σ.singleton_mem (s l))

/-- A lineage-labelled tree extending the taxon-labelled tree. -/
noncomputable def SpeciesTree.extend (σ : SpeciesTree X) (s : L → X) (hs : Function.Surjective s) : SpeciesTree L :=
  let h := (σ.isHierarchy.2.2.image (samplesIn s) (fun A ha => nonempty_pre hs (σ.nonempty_of_mem A ha))
    (fun _ _ h => (preLE hs _ _).2 h) (fun h => disjoint_left.2 fun _ ha hb =>
      disjoint_left.1 h (mem_samplesIn.1 ha) (mem_samplesIn.1 hb))).union_singletons univ
  { clusters := extendClusters σ.clusters s
    univ_mem := by simpa using pre_mem s σ.univ_mem
    singleton_mem := fun l => extend_cases.2 (Or.inr ⟨l, rfl⟩)
    nonempty_of_mem := h.1
    laminar := h.2
    length := fun B => if B.image s = univ then 1 else σ.length (B.image s)
    length_pos := fun B hB _ => by
      split_ifs with h
      · exact one_pos
      · exact σ.length_pos _ (image_extendClusters σ hs ▸ mem_image_of_mem (image s) hB) h }

omit [Fintype X] in
private theorem sampled_pre (s : L → X) (A : Finset X) : sampledForest s A = sampledForest id (samplesIn s A) := by
  simp [sampledForest, samplesIn]

private theorem child_pre (σ : SpeciesTree X) {s : L → X} (hs : Function.Surjective s)
    {A : Finset X} (h2 : 2 ≤ #A) :
    childClusters (σ.extend s hs).clusters (samplesIn s A) = (childClusters σ.clusters A).image (samplesIn s) := by
  have hlt {B C : Finset X} : samplesIn s B ⊂ samplesIn s C ↔ B ⊂ C := (preEmb hs).lt_iff_lt
  have child B (hB : B ∈ childClusters σ.clusters A) :
      samplesIn s B ∈ childClusters (σ.extend s hs).clusters (samplesIn s A) := by
    change samplesIn s B ∈ childClusters (extendClusters σ.clusters s) (samplesIn s A)
    have := (nonempty_pre hs (σ.nonempty_of_mem B (child_mem hB))).ne_empty
    grind [mem_childClusters, extend_cases, ssubset_singleton_iff]
  refine Subset.antisymm (fun C hC => ?_) (image_subset_iff.2 child)
  obtain ⟨l, hl⟩ := (σ.extend s hs).nonempty_of_mem C (child_mem hC)
  obtain ⟨B, hB, hlB⟩ := σ.isHierarchy.exists_mem_childClusters h2
    (mem_samplesIn.1 ((child_lt hC).subset hl))
  refine mem_image.2 ⟨B, hB, ?_⟩
  by_contra hne
  exact disjoint_left.1 ((σ.extend s hs).isHierarchy.disjoint_of_mem_childClusters (child B hB) hC hne)
    (mem_samplesIn.2 hlB) hl

/-- A sampling map and the extended species tree give the same law. -/
theorem SpeciesTree.unrootedDist_extend (σ : SpeciesTree X) {s : L → X} (hs : Function.Surjective s) :
    (σ.extend s hs).unrootedDist id = σ.unrootedDist s := by
  let τ := σ.extend s hs
  have h := forestDist_push (MonoidHom.id (ClusterFamily L)) (preEmb hs).toEmbedding
    σ.isHierarchy (sampled_pre s) (len := σ.length) (len' := τ.length) (H' := τ.clusters)
    (fun A hA => ?_) (fun A _ F _ => by
      change pushD id (populationKernel σ.length A F) = populationKernel τ.length (samplesIn s A) F
      rw [pushD_id]
      by_cases h : A = univ <;> simp [populationKernel, pre_eq_top hs, τ, SpeciesTree.extend, image_pre hs, h]) σ.univ_mem
  · unfold SpeciesTree.unrootedDist SpeciesTree.rootedDist
    exact congrArg (pushD unroot) (by simpa [preEmb] using h.symm)
  · change childClusters τ.clusters (samplesIn s A) = _ ∨ law (pushD id _) = law (τ.entering id (samplesIn s A))
    by_cases h2 : 2 ≤ #A
    · exact Or.inl (child_pre σ hs h2)
    · have hn := (σ.nonempty_of_mem A hA).card_pos
      obtain ⟨x, rfl⟩ := card_eq_one.1 (by omega : #A = 1)
      right
      rw [pushD_id, entering_of_small_children σ.isHierarchy σ.length s (by simp [σ.isHierarchy.childClusters_singleton]),
        sampled_pre, entering_of_small_children τ.isHierarchy]
      intro B hB
      have hlt {A : Finset X} : samplesIn s A ⊂ samplesIn s {x} ↔ A = ∅ :=
        (preEmb hs).lt_iff_lt.trans ssubset_singleton_iff
      have hn (A) (hA : A ∈ σ.clusters) := (σ.nonempty_of_mem A hA).ne_empty
      have hsng (l : L) : #(samplesIn id {l}) ≤ 1 := by simp [samplesIn, filter_eq']
      have hc : B ∈ extendClusters σ.clusters s := child_mem hB
      have hb := child_lt hB
      grind [extend_cases]

/-- Recover the original tree, including the pendant edges with at least two samples. -/
theorem SpeciesTree.sameRootedMetricTree_of_extend (hX : 2 ≤ Fintype.card X)
    (σ τ : SpeciesTree X) {s : L → X} (hs : Function.Surjective s)
    (h : (σ.extend s hs).SameRootedMetricTree (τ.extend s hs)) :
    σ.SameRootedMetricTree τ ∧ ∀ x, 2 ≤ #(univ.filter fun l => s l = x) → σ.length {x} = τ.length {x} := by
  have hc : σ.clusters = τ.clusters := by
    simpa only [SpeciesTree.extend, image_extendClusters _ hs] using congrArg (image (image s)) h.1
  have key (A : Finset X) (hA : A ∈ σ.clusters) (h2 : 2 ≤ #(samplesIn s A)) (hu : A ≠ univ) :
      σ.length A = τ.length A := by
    have e := h.2 (samplesIn s A) (pre_mem s hA) h2 (mt (pre_eq_top hs).1 hu)
    simpa [SpeciesTree.extend, image_pre hs, hu] using e
  refine ⟨⟨hc, fun A hA h2 => key A hA (h2.trans (card_pre hs A))⟩, fun x hx =>
    key {x} (σ.singleton_mem x) (by simpa [samplesIn] using hx)
      ((card_lt_iff_ne_univ _).1 (by simp; omega))⟩

end ADR11
