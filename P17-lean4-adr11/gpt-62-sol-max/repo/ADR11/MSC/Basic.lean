module

public import ADR11.Coalescent.Absorption

/-! Support and normalization of the multispecies coalescent recursion. -/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] {L : Type*} [Fintype L] [DecidableEq L]

/-- A hierarchy of clusters on `X`. -/
def IsHierarchy (H : ClusterFamily X) : Prop :=
  univ ∈ H ∧ (∀ x : X, {x} ∈ H) ∧ IsForest H

theorem SpeciesTree.isHierarchy (σ : SpeciesTree X) : IsHierarchy σ.clusters :=
  ⟨σ.univ_mem, σ.singleton_mem, σ.nonempty_of_mem, σ.laminar⟩

/-- The distribution of the forest entering the population above `A`: the union of the
independent forests leaving the populations of the children of `A`, together with the singletons
of the lineages sampled at `A`. -/
noncomputable def enteringDist (H : ClusterFamily X) (len : Finset X → ℝ) (s : L → X)
    (A : Finset X) (F : ClusterFamily L) : ℝ :=
  pushD (fun f : childClusters H A → ClusterFamily L => univ.sup f ∪ sampledForest s A)
    (fun f => ∏ B : childClusters H A, forestDist H len s B (f B)) F

open scoped Matrix in
theorem forestDist_eq (H : ClusterFamily X) (len : Finset X → ℝ) (s : L → X) (A : Finset X) :
    forestDist H len s A = enteringDist H len s A ᵥ* populationKernel len A := by
  funext G
  unfold Matrix.vecMul dotProduct enteringDist
  rw [pushD_test, forestDist]

noncomputable abbrev SpeciesTree.entering (σ : SpeciesTree X) (s : L → X) :=
  enteringDist σ.clusters σ.length s

noncomputable abbrev SpeciesTree.exiting (σ : SpeciesTree X) (s : L → X) :=
  forestDist σ.clusters σ.length s

theorem mem_childClusters {H : ClusterFamily X} {A B : Finset X} :
    B ∈ childClusters H A ↔ B ∈ H ∧ B ⊂ A ∧ ∀ C ∈ H, B ⊂ C → ¬ C ⊂ A :=
  mem_filter

theorem child_lt {H : ClusterFamily X} {A B : Finset X} (h : B ∈ childClusters H A) : B ⊂ A :=
  (mem_childClusters.1 h).2.1

theorem child_mem {H : ClusterFamily X} {A B : Finset X} (h : B ∈ childClusters H A) : B ∈ H :=
  (mem_childClusters.1 h).1

theorem children_as_roots (H : ClusterFamily X) (A : Finset X) :
    childClusters H A = roots (H.filter (· ⊂ A)) := by
  grind [mem_childClusters, mem_roots]

theorem exists_child_superset {H : ClusterFamily X} {A B : Finset X} (hB : B ∈ H) (hBA : B ⊂ A) :
    ∃ C ∈ childClusters H A, B ⊆ C := by
  rw [children_as_roots]
  exact exists_mem_roots_subset (mem_filter.2 ⟨hB, hBA⟩)

/-- In a hierarchy, the children of a cluster with at least two elements partition it, and a
singleton has no children. -/
theorem IsHierarchy.childClusters_singleton {H : ClusterFamily X} (hH : IsHierarchy H) (x : X) :
    childClusters H {x} = ∅ := by
  have := hH.2.2.1
  grind [mem_childClusters, ssubset_singleton_iff]

/-- Two distinct children of a cluster of a hierarchy are disjoint. -/
theorem IsHierarchy.disjoint_of_mem_childClusters {H : ClusterFamily X} (hH : IsHierarchy H)
    {A : Finset X} : (childClusters H A : Set (Finset X)).PairwiseDisjoint id := by
  rw [children_as_roots]
  exact (hH.2.2.subset (filter_subset _ _)).disjoint_of_mem_roots

/-- The lineages sampled within a cluster. -/
def samplesIn (s : L → X) (A : Finset X) : Finset L := univ.filter fun l => s l ∈ A

omit [Fintype X] [DecidableEq L] in
@[simp] theorem mem_samplesIn {s : L → X} {A : Finset X} {l : L} : l ∈ samplesIn s A ↔ s l ∈ A := by
  simp [samplesIn]

omit [Fintype X] in
theorem mem_sampledForest {s : L → X} {A : Finset X} {C : Finset L} :
    C ∈ sampledForest s A ↔ ∃ l, s l ∈ A ∧ {l} = C := by
  simp [sampledForest]

omit [Fintype X] in
theorem sampledForest_eq_image (s : L → X) (A : Finset X) :
    sampledForest s A = (samplesIn s A).image (fun l => {l}) := rfl

omit [Fintype X] in
theorem sampledForest_mono {s : L → X} {A B : Finset X} (h : A ⊆ B) : sampledForest s A ⊆ sampledForest s B :=
  image_subset_image (fun _ hl => mem_samplesIn.2 (h (mem_samplesIn.1 hl)))

/-- Forests supported by a population's samples. -/
abbrev SampleForestOn (s : L → X) (A : Finset X) (F : ClusterFamily L) : Prop :=
  IsForest F ∧ sampledForest s A ⊆ F ∧ lineages F = samplesIn s A

/-- A nonzero assignment of child histories gives a valid entering forest. -/
private theorem assignment_support {H : ClusterFamily X} (hH : IsHierarchy H)
    {len : Finset X → ℝ} {s : L → X} {A : Finset X} {f : childClusters H A → ClusterFamily L}
    (ih : ∀ B : childClusters H A, forestDist H len s B (f B) ≠ 0 → SampleForestOn s B (f B))
    (hp : (∏ B : childClusters H A, forestDist H len s B (f B)) ≠ 0) :
    SampleForestOn s A (univ.sup f ∪ sampledForest s A) := by
  have hf (B : childClusters H A) := ih B (prod_ne_zero_iff.1 hp B (mem_univ _))
  have sub (B : childClusters H A) {C : Finset L} (hC : C ∈ f B) : C ⊆ samplesIn s B :=
    (hf B).2.2 ▸ subset_lineages hC
  have hsup : IsForest (univ.sup f) := by
    have hd B E C D (hc : C ∈ f B) (hd : D ∈ f E) (e : B ≠ E) : Disjoint C D := by
      have h := hH.disjoint_of_mem_childClusters B.2 E.2 (e ∘ Subtype.ext)
      exact disjoint_left.2 fun l hl hm => disjoint_left.1 h
        (mem_samplesIn.1 (sub B hc hl)) (mem_samplesIn.1 (sub E hd hm))
    have F B := (hf B).1
    simp only [IsForest] at F ⊢
    grind [mem_sup]
  refine ⟨hsup.union_singletons _, subset_union_right, ?_⟩
  simp only [lineages, sup_union, sampledForest_eq_image, sup_image, Function.id_comp,
    sup_singleton_eq_self, sup_eq_right, sup_eq_biUnion univ f, sup_biUnion]
  refine Finset.sup_le fun B _ => ?_
  change lineages (f B) ⊆ samplesIn s A
  rw [(hf B).2.2]
  exact fun _ h => mem_samplesIn.2 ((child_lt B.2).subset (mem_samplesIn.1 h))

/-- Each population kernel is normalized and respects forest support. -/
private theorem population_spec (len : Finset X → ℝ) (A : Finset X) {F : ClusterFamily L} (hF : IsForest F) :
    (∀ G, populationKernel len A F G ≠ 0 → IsForest G ∧ F ⊆ G ∧ lineages G = lineages F) ∧
      (∑ G, populationKernel len A F G = 1) ∧
      ((A ≠ univ → 0 ≤ len A) → ∀ G, 0 ≤ populationKernel len A F G) := by
  unfold populationKernel
  split_ifs with hA
  · refine ⟨fun G h => ?_, kingmanAbsorption_sum hF, fun _ => kingmanAbsorption_nonneg hF⟩
    rw [kingmanAbsorption_apply hF] at h
    exact mergeCount_support hF (right_ne_zero_of_mul h)
  · exact ⟨fun _ => kingmanTransition_support hF, kingmanTransition_sum hF _,
      fun h => kingmanTransition_nonneg (h hA) F⟩

/-- The recursion preserves support and total mass, and is nonnegative at nonnegative lengths. -/
private theorem forestDist_spec {H : ClusterFamily X} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) (A : Finset X) :
    (∀ G, forestDist H len s A G ≠ 0 → SampleForestOn s A G) ∧ (∑ G, forestDist H len s A G = 1) ∧
    ((∀ B ∈ H, B ≠ univ → 0 ≤ len B) → A ∈ H → ∀ G, 0 ≤ forestDist H len s A G) := by
  induction A using Finset.strongInduction with
  | H A ih =>
    let p (f : childClusters H A → ClusterFamily L) := ∏ B : childClusters H A, forestDist H len s B (f B)
    have enter (f) (h : p f ≠ 0) : SampleForestOn s A (univ.sup f ∪ sampledForest s A) :=
      assignment_support hH (fun B => (ih B (child_lt B.2)).1 _) h
    refine ⟨?_, ?_, ?_⟩
    · intro G hG
      rw [forestDist] at hG
      obtain ⟨f, -, hf⟩ := exists_ne_zero_of_sum_ne_zero hG
      obtain ⟨hs, hb, hl⟩ := enter f (left_ne_zero_of_mul hf)
      obtain ⟨hg, hu, hlg⟩ := (population_spec len A hs).1 G (right_ne_zero_of_mul hf)
      exact ⟨hg, hb.trans hu, hlg.trans hl⟩
    · simp_rw [forestDist.eq_1 (A := A)]
      rw [sum_comm]
      simp_rw [← mul_sum]
      rw [sum_mul_congr (v := fun _ => 1) (fun f _ hf => (population_spec len A (enter f hf).1).2.1)]
      simp_rw [mul_one, p, ← Fintype.prod_sum]
      exact prod_eq_one fun B _ => (ih B (child_lt B.2)).2.1
    · intro hlen hA G
      rw [forestDist]
      refine sum_nonneg fun f _ => ?_
      change 0 ≤ p f * _
      by_cases h : p f = 0
      · simp [h]
      exact mul_nonneg (prod_nonneg fun B _ => (ih B (child_lt B.2)).2.2 hlen (child_mem B.2) _)
        ((population_spec len A (enter f h).1).2.2 (hlen A hA) G)

theorem forestDist_support {H : ClusterFamily X} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) {A : Finset X} {G : ClusterFamily L} (hG : forestDist H len s A G ≠ 0) :
    SampleForestOn s A G := (forestDist_spec hH len s A).1 G hG

theorem forestDist_sum {H : ClusterFamily X} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) (A : Finset X) : ∑ G, forestDist H len s A G = 1 := (forestDist_spec hH len s A).2.1

theorem enteringDist_support {H : ClusterFamily X} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) {A : Finset X} {F : ClusterFamily L} (hF : enteringDist H len s A F ≠ 0) :
    SampleForestOn s A F := by
  unfold enteringDist pushD at hF
  obtain ⟨f, -, hf⟩ := exists_ne_zero_of_sum_ne_zero hF
  split_ifs at hf with e
  · exact e ▸ assignment_support hH (fun _ => forestDist_support hH len s) hf
  · contradiction

/-! ### The children of a cluster of a hierarchy -/

/-- Every element of a cluster `A` with at least two elements lies in a child of `A`. -/
theorem IsHierarchy.exists_mem_childClusters {H : ClusterFamily X} (hH : IsHierarchy H)
    {A : Finset X} (hA : 2 ≤ #A) {x : X} (hx : x ∈ A) : ∃ B ∈ childClusters H A, x ∈ B := by
  have hxA : ({x} : Finset X) ⊂ A := by grind
  simpa using exists_child_superset (hH.2.1 x) hxA

theorem SpeciesTree.unrootedDist_nonneg (σ : SpeciesTree X) (s : L → X) (T : Finset (Finset L)) :
    0 ≤ σ.unrootedDist s T := by
  apply sum_nonneg fun G _ => ite_nonneg ?_ le_rfl
  exact (forestDist_spec σ.isHierarchy σ.length s univ).2.2
    (fun A hA hu => (σ.length_pos A hA hu).le) σ.univ_mem _

theorem SpeciesTree.unrootedDist_sum (σ : SpeciesTree X) (s : L → X) : ∑ T, σ.unrootedDist s T = 1 := by
  have h := pushD_test unroot (σ.rootedDist s) (fun _ => 1)
  simp only [mul_one] at h
  exact h.trans (forestDist_sum σ.isHierarchy σ.length s univ)

end ADR11
