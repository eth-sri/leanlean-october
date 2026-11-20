module

public import ADR11.Trees.Hierarchy
public import ADR11.MSC.Independent

/-! Dropping lineages is a lumping of Kingman's coalescent and commutes with the population
recursion. -/

@[expose] public section

namespace ADR11
open Finset
open scoped Matrix Independent
open Independent

variable {L X : Type*} [Fintype L] [DecidableEq L] [Fintype X] [DecidableEq X]

omit [Fintype L] in
private theorem trace_not_disjoint {S A B : Finset L} (h : trace S A ⊆ trace S B) (hA : (trace S A).Nonempty) :
    ¬ Disjoint A B := by
  exact fun hd => hA.ne_empty (disjoint_self.1 ((trace_disjoint hd).mono_right h))

omit [Fintype L] in
private theorem IsForest.ssubset_of_trace {H : ClusterFamily L} (hH : IsForest H) {S A B : Finset L}
    (hA : A ∈ H) (hB : B ∈ H) (hn : (trace S A).Nonempty) (h : trace S A ⊂ trace S B) : A ⊂ B := by
  have hn' : ¬ B ⊆ A := fun e => h.not_ge (subtype_mono e)
  have := hH.2 A hA B hB
  have := trace_not_disjoint h.subset hn
  grind

omit [Fintype L] in
private theorem trace_injOn {S : Finset L} {F : ClusterFamily L}
    (hd : (F : Set (Finset L)).PairwiseDisjoint id) :
    Set.InjOn (trace S) (F.filter fun A => (trace S A).Nonempty) := by
  intro A ha B hb e
  by_contra h
  exact trace_not_disjoint (e ▸ Subset.rfl) (mem_filter.1 ha).2
    (hd (mem_filter.1 ha).1 (mem_filter.1 hb).1 h)

private theorem roots_traceFamily (S : Finset L) {F : ClusterFamily L} (hF : IsForest F) :
    roots (restrictClusters S F) = restrictClusters S (roots F) := by
  ext B
  rw [mem_roots, mem_restrictClusters, mem_restrictClusters]
  constructor
  · rintro ⟨⟨hn, A, hA, rfl⟩, hm⟩
    obtain ⟨C, hC, hAC⟩ := exists_mem_roots_subset hA
    have le := subtype_mono (p := (· ∈ S)) hAC
    have := hn.mono le
    have := roots_subset F hC
    grind [mem_restrictClusters]
  · rintro ⟨hn, A, hA, rfl⟩
    refine ⟨⟨hn, A, roots_subset F hA, rfl⟩, ?_⟩
    intro C hc le
    obtain ⟨-, B, hb, rfl⟩ := mem_restrictClusters.1 hc
    by_contra he
    have ab := hF.ssubset_of_trace (roots_subset F hA) hb hn (le.ssubset_of_ne (Ne.symm he))
    exact ab.ne ((mem_roots.1 hA).2 B hb ab.subset).symm

private theorem merge_trace (S : Finset L) {F P : ClusterFamily L}
    (hP : P ∈ mergePairs F) :
    restrictClusters S (mergeAt F P) =
      if ∀ C ∈ P, (trace S C).Nonempty then mergeAt (restrictClusters S F) (P.image (trace S))
      else restrictClusters S F := by
  obtain ⟨hP, hc⟩ := mem_powersetCard.1 hP
  obtain ⟨A, B, _, rfl⟩ := card_eq_two.1 hc
  have ha : A ∈ F := roots_subset F (hP (by simp))
  have hb : B ∈ F := roots_subset F (hP (by simp))
  have ht : trace S (A ∪ B) = trace S A ∪ trace S B := by ext; simp
  by_cases a : (trace S A).Nonempty <;> by_cases b : (trace S B).Nonempty <;>
    simp_all [restrictClusters, mergeAt, filter_insert, union_nonempty,
      not_nonempty_iff_eq_empty] <;> grind

private theorem trace_sum_generator (S : Finset L) {F : ClusterFamily L} (hF : IsForest F)
    (u : ClusterFamily S → ℝ) :
    ∑ G, kingmanGenerator F G * u (restrictClusters S G) =
      ∑ G, kingmanGenerator (restrictClusters S F) G * u G := by
  let V := (roots F).filter (fun A => (trace S A).Nonempty)
  have hV : V.image (trace S) = roots (restrictClusters S F) := (roots_traceFamily S hF).symm
  have hf : Set.InjOn (trace S) V := trace_injOn hF.disjoint_of_mem_roots
  have pairs : (V.powersetCard 2).image (·.image (trace S)) = (V.image (trace S)).powersetCard 2 := by
    rw [powersetCard_eq_filter, powersetCard_eq_filter, powerset_image, filter_image]
    congr 1
    exact filter_congr fun Q h => by rw [card_image_of_injOn (hf.mono (mem_powerset.1 h))]
  have hs : V.powersetCard 2 ⊆ mergePairs F := powersetCard_mono (filter_subset _ _)
  simp only [hF.sum_generator_pairs, (hF.traceFamily S).sum_generator_pairs, mergePairs, ← hV, ← pairs]
  rw [← sum_subset hs, sum_image]
  · exact sum_congr rfl fun P hP => by rw [merge_trace S (hs hP), ite_eq_left (by grind)]
  · exact (image_injOn_powerset_of_injOn hf).mono (fun _ h => mem_powerset.2 (mem_powersetCard.1 h).1)
  · intro P hp hn
    rw [merge_trace S hp, ite_eq_right (by grind), sub_self]

private theorem traceFamily_sampled (S A : Finset L) :
    restrictClusters S (sampledForest id A) = sampledForest Subtype.val A := by
  ext B
  simp only [mem_restrictClusters, mem_sampledForest, exists_exists_and_eq_and, id_eq]
  constructor
  · rintro ⟨⟨x, hx⟩, y, hy, rfl⟩
    have e : x.val = y := by simpa using hx
    subst y
    simp [hy]
  · rintro ⟨x, hx, rfl⟩
    exact ⟨singleton_nonempty _, _, hx, trace_singleton S x⟩

/-! ### Pruning populations and collapsing chains -/

omit [Fintype X] in
private theorem sampled_trace (S A : Finset X) :
    sampledForest Subtype.val A = sampledForest id (trace S A) := by simp [sampledForest]

/-- At a branching population the trace strictly shrinks on every proper descendant. -/
private theorem trace_children {H : ClusterFamily X} (hH : IsForest H) {S A : Finset X}
    (hA : A ∈ H) (hd : ∀ B ∈ H, B ⊂ A → trace S B ⊂ trace S A) :
    restrictClusters S (childClusters H A) = childClusters (restrictClusters S H) (trace S A) := by
  rw [children_as_roots H, children_as_roots, ← roots_traceFamily _ (hH.subset (filter_subset _ _))]
  simp only [restrictClusters, filter_image, filter_filter]
  congr 2
  exact filter_congr fun B hB => ⟨fun ⟨h, hn⟩ => ⟨hn, hd B hB h⟩,
    fun ⟨hn, h⟩ => ⟨hH.ssubset_of_trace hB hA hn h, hn⟩⟩

private noncomputable def cumulative (σ : SpeciesTree X) (S A : Finset X) : ℝ :=
  ∑ C ∈ σ.clusters with C ⊆ A ∧ trace S C = trace S A, σ.length C

/-- Within the parent's proper descendants, the fibre of a nonempty child trace lies below that child. -/
private theorem child_fiber {H : ClusterFamily X} (hH : IsHierarchy H) {S A B : Finset X}
    (hB : B ∈ childClusters H A) (hn : (trace S B).Nonempty) :
    H.filter (fun C => C ⊂ A ∧ trace S C = trace S B) =
      H.filter (fun C => C ⊆ B ∧ trace S C = trace S B) := by
  have key C hC hCA (e : trace S C = trace S B) :=
    hH.subset_of_mem_childClusters hB hC hCA (trace_not_disjoint (e.ge) hn)
  ext C
  simp only [mem_filter]
  grind [child_lt]

/-- Children with empty trace contribute the unit law and can be dropped. -/
private theorem entering_trace_prod (σ : SpeciesTree X) {S A : Finset X} :
    law (σ.entering Subtype.val A) = MonoidAlgebra.single (sampledForest id (trace S A)) 1 *
      ∏ B ∈ (childClusters σ.clusters A).filter (fun B => (trace S B).Nonempty),
        law (σ.exiting Subtype.val B) := by
  rw [SpeciesTree.entering, law_entering, sampled_trace S]
  congr 1
  refine (prod_filter_of_ne fun B _ h => ?_).symm
  contrapose! h
  have he : samplesIn (Subtype.val : S → X) B = ∅ := by
    convert h using 1
    ext; simp
  rw [law_forestDist_small σ.isHierarchy σ.length _ (A := B) (by simp [he]), sampledForest_eq_image, he]
  rfl

private theorem exiting_eq (σ : SpeciesTree X) (s : L → X) (A : Finset X) :
    σ.exiting s A = σ.entering s A ᵥ* populationKernel σ.length A := forestDist_eq ..

set_option backward.isDefEq.respectTransparency false in
private theorem prune (σ : SpeciesTree X) {S : Finset X} (hS : S.Nonempty)
    (A : Finset X) (hA : A ∈ σ.clusters) (hn : (trace S A).Nonempty) :
    σ.exiting Subtype.val A =
      (σ.restrict S hS).entering id (trace S A) ᵥ*
        populationKernel (cumulative σ S) A := by
  let τ := σ.restrict S hS
  induction A using Finset.strongInduction with
  | H A ih =>
    rw [exiting_eq]
    by_cases h : ∃ B ∈ childClusters σ.clusters A, trace S B = trace S A
    · obtain ⟨B, hB, he⟩ := h
      have hnB : (trace S B).Nonempty := he.symm ▸ hn
      have enter : σ.entering (Subtype.val : S → X) A = σ.exiting Subtype.val B := by
        apply law_injective
        rw [entering_trace_prod σ, prod_eq_single_of_mem B (mem_filter.2 ⟨hB, hnB⟩)]
        · rw [← he, ← sampled_trace S]
          exact sample_mul_law _ _ (fun F h => (forestDist_support σ.isHierarchy σ.length _ h).2.1)
        · intro C hc hn'
          obtain ⟨hC, hCn⟩ := mem_filter.1 hc
          exact (trace_not_disjoint (he ▸ subtype_mono (child_lt hC).subset) hCn
            (σ.isHierarchy.disjoint_of_mem_childClusters hC hB hn')).elim
      have len : cumulative σ S A = σ.length A + cumulative σ S B := by
        unfold cumulative
        rw [← add_sum_erase _ _ (a := A) (by simp [hA]), ← child_fiber σ.isHierarchy hB hnB]
        congr 2
        ext C
        simp [Finset.ssubset_iff_subset_ne, he, and_assoc, and_comm]
      rw [enter, ih B (child_lt hB) (child_mem hB) hnB,
        populationKernel, ite_eq_right (show B ≠ univ from ne_top_of_lt (child_lt hB)), Matrix.vecMul_vecMul]
      simp only [populationKernel, len, he]
      funext G
      refine sum_mul_congr fun F _ hF => ?_
      split_ifs
      · exact kingmanTransition_mul_kingmanAbsorption (enteringDist_support τ.isHierarchy τ.length id hF).1 _ _
      · rw [add_comm, kingmanTransition_add]
    · have hd C (hC : C ∈ σ.clusters) (hCA : C ⊂ A) : trace S C ⊂ trace S A := by
        obtain ⟨B, hB, hCB⟩ := exists_child_superset hC hCA
        exact (subtype_mono hCB).trans_ssubset
          ((subtype_mono (child_lt hB).subset).ssubset_of_ne fun e => h ⟨B, hB, e⟩)
      have hE : law (σ.entering Subtype.val A) = law (τ.entering id (trace S A)) := by
        rw [entering_trace_prod σ, SpeciesTree.entering, law_entering, SpeciesTree.restrict_clusters,
          ← trace_children σ.isHierarchy.2.2 hA hd, restrictClusters, prod_image (trace_injOn σ.isHierarchy.disjoint_of_mem_childClusters)]
        congr 1
        refine prod_congr rfl fun B hB => ?_
        obtain ⟨hB, hnB⟩ := mem_filter.1 hB
        change law (σ.exiting Subtype.val B) = law (τ.exiting id (trace S B))
        have hlt := child_lt hB
        have ht := hd B (child_mem hB) hlt
        have len : cumulative σ S B = σ.restrictLength S (trace S B) := by
          rw [cumulative, ← child_fiber σ.isHierarchy hB hnB, SpeciesTree.restrictLength]
          congr 1
          ext C
          simp only [mem_filter]
          have key (hc : C ∈ σ.clusters) (e : trace S C = trace S B) :=
            σ.isHierarchy.2.2.ssubset_of_trace hc hA (e.symm ▸ hnB) (e.symm ▸ ht)
          grind
        rw [ih B hlt (child_mem hB) hnB, exiting_eq]
        simp only [populationKernel, ite_eq_right (show B ≠ univ from ne_top_of_lt hlt),
          ite_eq_right (show trace S B ≠ univ from ne_top_of_lt ht), len, SpeciesTree.restrict_length, τ]
      have len : cumulative σ S A = σ.length A := by
        rw [cumulative, sum_eq_single_of_mem A (by simp [hA])]
        grind
      simp [law_injective hE, populationKernel, len, τ]

/-- Lemma 5: each induced unrooted distribution is the marginal on the retained taxa. -/
theorem SpeciesTree.unrootedDist_restrict (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    (σ.restrict S hS).unrootedDist id = pushD (restrictSplits S) (σ.unrootedDist id) := by
  let f : ClusterFamily X →* ClusterFamily S :=
    { toFun := restrictClusters S
      map_one' := rfl
      map_mul' F G := by simp [restrictClusters, image_union, filter_union] }
  have drop : pushD (restrictClusters S) (σ.rootedDist id) = σ.rootedDist Subtype.val :=
    forestDist_push f (Function.Embedding.refl (Finset X)) σ.isHierarchy (traceFamily_sampled S)
      (fun _ _ => Or.inl image_id.symm)
      (fun _ _ _ hF => population_push _ (trace_sum_generator S) hF (hF.traceFamily S) Iff.rfl rfl) σ.univ_mem
  have prune_root : (σ.restrict S hS).rootedDist id = σ.rootedDist Subtype.val := by
    change (σ.restrict S hS).exiting id univ = σ.exiting Subtype.val univ
    rw [prune σ hS univ σ.univ_mem (by simpa [trace] using hS),
      show trace S univ = univ from subtype_univ _, exiting_eq]
    simp [populationKernel]
  change pushD unroot _ = pushD (restrictSplits S) (pushD unroot _)
  rw [prune_root, ← drop]
  ext U
  simp [Function.comp_def, unroot_restrictClusters]

/-- Equal distributions agree on every induced subtree. -/
theorem unrootedDist_restrict_eq {σ σ' : SpeciesTree X}
    (h : σ.unrootedDist id = σ'.unrootedDist id) (S : Finset X) (hS : S.Nonempty) :
    (σ.restrict S hS).unrootedDist id = (σ'.restrict S hS).unrootedDist id := by
  rw [σ.unrootedDist_restrict, σ'.unrootedDist_restrict, h]

end ADR11
