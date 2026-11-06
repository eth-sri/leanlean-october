module

public import ADR11.Trees.Hierarchy
/-!
# Marginalization

The paper's Lemma 5 is "clear from the structure of the coalescent model". It combines two facts:

* *Dropping lineages* (`forestDist_comp_subset`): the forest formed by a subset of the lineages
  is distributed as the multispecies coalescent of that subset. Kingman's coalescent is
  consistent: restricting a forest to a subset of the lineages lumps the chain into Kingman's
  coalescent on the subset (`kingmanTransition_lump`, `kingmanAbsorption_lump`).
* *Pruning the species tree* (`rootedDist_restrict`): when only taxa in `S` are sampled, the
  populations without lineages do nothing, populations in a chain with the same lineages merge
  into one population whose length is the sum (`kingmanTransition_add`), and the populations above
  the most recent common ancestor of `S` merge into the population above the root.

* `restrictClusters R F`: the restriction of a forest on `L` to the lineages `R`, along an
  embedding `R : R ↪ L`.
* `restrictSplits R T`: the restriction of an unrooted tree (given by the sides of its splits)
  to the lineages `R`.

## Main results

* `kingmanTransition_lump`, `kingmanAbsorption_lump`: lumpability of Kingman's coalescent. The
  generators intertwine, `Q M = M Q'` on the rows of forests, where `M` is the restriction map:
  merging two roots that both meet the range of `R` merges their traces, and the other merges do
  not change the restriction.
* `forestDist_comp_subset`, `SpeciesTree.rootedDist_comp_subset`,
  `SpeciesTree.unrootedDist_comp_subset`: dropping lineages.
* `SpeciesTree.rootedDist_restrict`: pruning the species tree. It is proved by strong induction
  on the clusters `A ≠ univ` meeting `S`: the forest leaving `A` is the forest entering the trace
  `A ∩ S` in `σ(S)`, evolved for the sum of the lengths of the clusters `A' ⊆ A` with the same
  trace (a chain).
* `unroot_restrictClusters`: unrooting commutes with restricting (for any family of clusters).
-/

@[expose] public section

namespace ADR11

open Finset
open scoped Matrix

variable {X : Type*} [Fintype X] [DecidableEq X]
variable (σ : SpeciesTree X)
variable {L : Type*} [Fintype L] [DecidableEq L]

variable {H : Family X} {F : Family L} {S A B B₀ : Finset X} (R : Finset L)

/-! ### Restricting forests -/

theorem IsForest.restrictClusters (hF : IsForest F) (R : Finset L) :
    IsForest (restrictClusters R F) := by
  have := @Finset.mem_subtype L (Membership.mem R) _
  grind [-Subtype, IsForest, mem_restrictClusters, Finset.subtype_mono, disjoint_left]

/-- The trace is injective on the roots meeting the range of `R`. -/
private theorem marg_tr_inj (hF : IsForest F) (R : Finset L)
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) (hmeet : (A.trace R).Nonempty)
    (h : (A.trace R) = B.trace R) : A = B := by
  have := @Finset.mem_subtype L (Membership.mem R) _
  grind [-Subtype, hF.eq_of_mem_roots_of_mem]

/-- The roots of the restriction of a forest are the traces of its roots meeting the range. -/
private theorem marg_mem_roots_restrictClusters (hF : IsForest F)
    (R : Finset L) {D : Finset R} :
    D ∈ roots (restrictClusters R F) ↔
      ∃ A ∈ roots F, (A.trace R).Nonempty ∧ (A.trace R) = D := by
  have := @Finset.mem_subtype L (Membership.mem R) _
  have hm {C D : Finset L} (h : C ⊆ D) : C.trace R ⊆ D.trace R := Finset.subtype_mono h
  grind (splits := 25) [-Subtype, mem_roots, mem_restrictClusters, hF.eq_of_mem_roots_of_mem,
    subtype_mem_restrictClusters (S := R) (H := F),
    exists_mem_roots_subset (F := F)]

/-- The restriction of a merge: merging two roots that both meet the range of `R` merges their
traces; otherwise the restriction does not change. -/
private theorem marg_restrictClusters_merge
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) :
    restrictClusters R (insert (A ∪ B) F) =
      if (A.trace R).Nonempty ∧ (B.trace R).Nonempty then
        insert ((A.trace R) ∪ B.trace R)
          (restrictClusters R F)
      else restrictClusters R F := by
  have hu : (A ∪ B).trace R = A.trace R ∪ B.trace R := by ext; simp
  have ha := subtype_mem_restrictClusters (S := R) (roots_subset F hA)
  have hb := subtype_mem_restrictClusters (S := R) (roots_subset F hB)
  by_cases hAm : (A.trace R).Nonempty <;> by_cases hBm : (B.trace R).Nonempty <;>
    simp_all [restrictClusters, ← subtype_nonempty_iff, filter_insert, image_insert]

/-- The merges of `F` whose restriction differs from the restriction of `F`: the merges of two
roots that both meet the range of `R`. -/
private theorem marg_mem_merges_ne (hF : IsForest F) (R : Finset L)
    {H : Family L} :
    (H ∈ merges F ∧ restrictClusters R H ≠ restrictClusters R F) ↔
      ∃ A ∈ roots F, ∃ B ∈ roots F, A ≠ B ∧ (A.trace R).Nonempty ∧ (B.trace R).Nonempty ∧
        H = insert (A ∪ B) F := by
  constructor
  · grind [-Subtype, ← mem_merges, ← marg_restrictClusters_merge]
  · rintro ⟨A, hA, B, hB, hAB, hAm, hBm, rfl⟩
    have hrA := (marg_mem_roots_restrictClusters hF R).2 ⟨A, hA, hAm, rfl⟩
    have hrB := (marg_mem_roots_restrictClusters hF R).2 ⟨B, hB, hBm, rfl⟩
    grind [-Subtype, ← mem_merges, marg_restrictClusters_merge R hA hB, marg_tr_inj hF R, union_not_mem_of_mem_roots]

/-- The key count behind lumpability: summing a function of the restriction over the merges of
`F` gives the sum over the merges of the restriction, plus the merges that do not change the
restriction. -/
private theorem marg_sum_kingmanGenerator (hF : IsForest F) (R : Finset L)
    (u : Family R → ℝ) :
    ∑ G, kingmanGenerator F G * u (restrictClusters R G) =
      ∑ G', kingmanGenerator (restrictClusters R F) G' * u G'  := by
  rw [hF.sum_kingmanGenerator_mul, (hF.restrictClusters R).sum_kingmanGenerator_mul]
  set rF := restrictClusters R F with hrF
  have hrFf : IsForest rF := hF.restrictClusters R
  set M₂ := (merges F).filter fun H => restrictClusters R H ≠ rF with hM₂
  -- the restriction maps `M₂` onto the merges of `rF`
  have himage : M₂.image (restrictClusters R) = merges rF := by
    ext H'
    simp only [hM₂, hrF, mem_image, mem_filter, marg_mem_merges_ne hF R]
    simp only [mem_merges, marg_mem_roots_restrictClusters hF R]
    constructor
    · rintro ⟨_, ⟨A, hA, B, hB, hAB, hAm, hBm, rfl⟩, rfl⟩
      rw [marg_restrictClusters_merge R hA hB, ite_eq_left ⟨hAm, hBm⟩]
      grind [-Subtype, marg_tr_inj hF R]
    · rintro ⟨_, ⟨A, hA, hAm, rfl⟩, _, ⟨B, hB, hBm, rfl⟩, hAB, rfl⟩
      refine ⟨insert (A ∪ B) F, ?_, ?_⟩ <;> grind [-Subtype, marg_restrictClusters_merge R hA hB]
  -- and is injective on `M₂`
  have hsum : ∑ H ∈ merges F, (u (restrictClusters R H) - u rF) =
      ∑ H' ∈ merges rF, (u H' - u rF) := by
    rw [← himage, sum_image (by
      simp only [Set.InjOn, mem_coe, hM₂, mem_filter, hrF, marg_mem_merges_ne hF R]
      rintro _ ⟨A₁, hA₁, B₁, hB₁, hAB₁, hA₁m, hB₁m, rfl⟩
        _ ⟨A₂, hA₂, B₂, hB₂, hAB₂, hA₂m, hB₂m, rfl⟩ h12
      rw [marg_restrictClusters_merge R hA₁ hB₁, ite_eq_left ⟨hA₁m, hB₁m⟩,
        marg_restrictClusters_merge R hA₂ hB₂, ite_eq_left ⟨hA₂m, hB₂m⟩] at h12
      have hr := fun {A} (hA : A ∈ roots F) (hAm : (A.trace R).Nonempty) =>
        (marg_mem_roots_restrictClusters hF R).2 ⟨A, hA, hAm, rfl⟩
      grind [-Subtype, IsForest.merge_eq_merge_iff, marg_tr_inj hF R]
    )]
    symm
    apply sum_subset (filter_subset _ _)
    intro H hH hn
    have : restrictClusters R H = rF := by simpa [hM₂, hH] using hn
    simp [this]
  simp only [sum_sub_distrib, sum_const, hF.card_merges, hrFf.card_merges,
    nsmul_eq_mul] at hsum
  linarith

/-- Lumpability of Kingman's coalescent, tested against a function `w` of the restriction. -/
private theorem marg_sum_kingmanTransition (hF : IsForest F)
    (R : Finset L) (t : ℝ) (w : Family R → ℝ) :
    ∑ G, kingmanTransition t F G * w (restrictClusters R G) =
      ∑ G', kingmanTransition t (restrictClusters R F) G' * w G' := by
  refine (
    hasSum_sum (s := univ) fun G _ =>
      (hasSum_matrix_exp_apply (t • kingmanGenerator (L := L)) F G).mul_right (w (restrictClusters R G))
  ).unique ?_
  convert! (
    hasSum_sum (s := univ) fun G' _ =>
      (hasSum_matrix_exp_apply (t • kingmanGenerator (L := R)) (restrictClusters R F) G').mul_right (w G')
  ) using 1
  funext n
  simp_rw [smul_pow, Matrix.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum]
  congr 2
  induction n generalizing F w with
  | zero => simp [Matrix.one_apply]
  | succ n ih =>
    change (kingmanGenerator ^ (n + 1) *ᵥ (w ∘ restrictClusters R)) F =
      (kingmanGenerator ^ (n + 1) *ᵥ w) (restrictClusters R F)
    simp only [pow_succ', ← Matrix.mulVec_mulVec]
    change ∑ H, kingmanGenerator F H * _ =
      ∑ H', kingmanGenerator (restrictClusters R F) H' * _
    rw [← marg_sum_kingmanGenerator hF R (kingmanGenerator ^ n *ᵥ w)]
    apply sum_congr rfl
    intro H _
    by_cases hz : kingmanGenerator F H = 0
    · simp [hz]
    · congr 1
      exact ih (by grind [-Subtype, ← hF.of_mem_merges, kingmanGenerator, ← mem_merges]) w

/-- Consistency of Kingman's coalescent (lumpability). -/
theorem kingmanTransition_lump (hF : IsForest F) (R : Finset L) (t : ℝ)
    (G' : Family R) :
    ∑ G, (if restrictClusters R G = G' then kingmanTransition t F G else 0) =
      kingmanTransition t (restrictClusters R F) G' := by
  simpa using marg_sum_kingmanTransition hF R t (fun G'' => if G'' = G' then 1 else 0)

/-! ### Dropping lineages -/

private theorem marg_restrictClusters_union (F₁ F₂ : Family L) :
    restrictClusters R (F₁ ∪ F₂) = restrictClusters R F₁ ∪ restrictClusters R F₂ := by
  unfold restrictClusters
  rw [filter_union, image_union]

private theorem marg_restrictClusters_sampledForest (s : L → X) (A : Finset X) :
    restrictClusters R (sampledForest s A) = sampledForest (s ∘ Subtype.val) A := by
  ext D
  simp only [mem_restrictClusters, mem_sampledForest]
  have := @Finset.mem_subtype L (Membership.mem R) _
  have ht (l : R) : ({(l : L)} : Finset L).trace R = {l} := by ext; simp
  grind [-Subtype, singleton_nonempty]

/-- A sum of the form `∑ b, [g b = c] ∑ a, [f a = b] p a` is a pushforward. -/
private theorem marg_sum_ite_comp {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [DecidableEq γ] (f : α → β) (g : β → γ) (p : α → ℝ) (c : γ) :
    ∑ b, (if g b = c then ∑ a, (if f a = b then p a else 0) else 0) =
      ∑ a, if g (f a) = c then p a else 0 := by
  simp_rw [ite_sum_zero, ← ite_and, and_comm (a := g _ = c), ite_and]
  rw [sum_comm]
  simp

/-- Dropping lineages: the multispecies coalescent of the lineages `R` (sampled through
`s ∘ Subtype.val`) is the restriction of the multispecies coalescent of the lineages `L`. -/
theorem forestDist_comp_subset (hH : IsHierarchy H)
    (len : Finset X → ℝ) (s : L → X) (R : Finset L)
    (G' : Family R) :
    forestDist H len (s ∘ Subtype.val) A G' =
      ∑ G, if restrictClusters R G = G' then forestDist H len s A G else 0 := by
  induction A using Finset.strongInduction generalizing G' with
  | H A ih =>
  have he : enteringDist H len (s ∘ Subtype.val) A =
      fun F' => ∑ F, if restrictClusters R F = F' then enteringDist H len s A F else 0 := by
    funext F'
    have hi (B : childClusters H A) := ih B (mem_childClusters.1 B.2).2.1
    unfold enteringDist
    simp_rw [hi, Fintype.prod_sum, prod_ite_zero]
    simp only [mem_univ, true_implies]
    simp only [← funext_iff]
    simp_rw [marg_sum_ite_comp,
      marg_restrictClusters_union, Finset.apply_sup_eq_sup_comp (restrictClusters R) (marg_restrictClusters_union R)
        (by simp [restrictClusters]), marg_restrictClusters_sampledForest, Function.comp_def]
  simp_rw [forestDist_eq_sum_entering, Matrix.vecMul, dotProduct, he, sum_mul,
    ite_mul, zero_mul]
  rw [sum_comm]
  simp only [sum_ite_eq, mem_univ, ite_true]
  conv_rhs =>
    simp only [ite_sum_zero]
    rw [sum_comm]
  apply sum_congr rfl
  intro F _
  by_cases h0 : enteringDist H len s A F = 0
  · simp [h0]
  · have hF := (enteringDist_support hH len s h0).1
    have ha : ∑ G, (if restrictClusters R G = G' then kingmanAbsorption F G else 0) =
        kingmanAbsorption (restrictClusters R F) G' := by
      have h1 := tendsto_finsetSum univ fun G _ =>
        (tendsto_kingmanTransition hF G).mul_const (if restrictClusters R G = G' then 1 else 0)
      simp [kingmanTransition_lump hF R] at h1
      exact tendsto_nhds_unique h1 (tendsto_kingmanTransition (hF.restrictClusters R) G')
    unfold populationKernel
    split_ifs
    all_goals
      first | rw [← ha] | rw [← kingmanTransition_lump hF R _ G']
      simp only [mul_sum, mul_ite, mul_zero]

/-! ### Pruning the species tree -/

private theorem marg_sum_pi_restrict {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Prop) [DecidablePred P] 
    (φ : ι → Family L → ℝ)
    (h0 : ∀ i, ¬ P i → ∀ F, φ i F = if F = ∅ then 1 else 0)
    (c F : Family L) :
    (∑ f : ι → Family L, if univ.sup f ∪ c = F then ∏ i, φ i (f i) else 0) =
      ∑ g : {i // P i} → Family L, if univ.sup g ∪ c = F then ∏ i : {i // P i}, φ i (g i) else 0 := by
  classical
  let E := Equiv.piEquivPiSubtypeProd P (fun _ => Family L)
  rw [← E.symm.sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun f _ => ?_
  have hn (i : {i // ¬ P i}) : ¬ P i := i.2
  simp_rw [← Fintype.prod_subtype_mul_prod_subtype P]
  simp [E, hn, h0, Subtype.property, Fintype.prod_ite_zero, ← funext_iff, mul_ite]
  simp_rw [← ite_and, and_comm (b := _ = fun _ : {i // ¬ P i} => (∅ : Family L)), ite_and]
  simp only [sum_ite_eq', mem_univ, ite_true]
  congr 3
  ext A
  simp [Finset.mem_sup]
  aesop

/-- The trace of a child of `A` meeting `S`, with a trace different from that of `A`, is a child
of the trace of `A` in the induced tree. -/
private theorem marg_subtype_mem_childClusters (hH : IsHierarchy H)
    (hA : A ∈ H) (hB : B ∈ childClusters H A) (hBS : (B ∩ S).Nonempty)
    (hne : B.trace S ≠ A.trace S) :
    B.trace S ∈ childClusters (restrictClusters S H) (A.trace S) := by
  obtain ⟨hBH, hBA, hBmax⟩ := mem_childClusters.1 hB
  refine mem_childClusters.2 ⟨subtype_mem_restrictClusters hBH (subtype_nonempty_iff.2 hBS),
    (subtype_mono hBA.subset).ssubset_of_ne hne, ?_⟩
  rintro E' hE' hBE' hE'A
  obtain ⟨E, hE, -, rfl⟩ := mem_restrictClusters.1 hE'
  obtain ⟨x, hx⟩ := subtype_nonempty_iff.2 hBS
  have := hH.2.2.2
  grind [Finset.subtype_mono, ← (@Finset.mem_subtype X (Membership.mem S) _), disjoint_left]

/-- If no child of `A` has the trace of `A`, every child of the trace of `A` in the induced tree
is the trace of a child of `A`. -/
private theorem marg_exists_child (hH : IsHierarchy H) (hH' : IsHierarchy (restrictClusters S H)) (hA : A ∈ H)
    (hbot : ∀ B ∈ childClusters H A, B.trace S ≠ A.trace S)
    {D : Finset S} (hD : D ∈ childClusters (restrictClusters S H) (A.trace S)) :
    ∃ B ∈ childClusters H A, (B ∩ S).Nonempty ∧ B.trace S = D := by
  obtain ⟨hDH, hDA, -⟩ := mem_childClusters.1 hD
  obtain ⟨x, hx⟩ := hH'.2.2.1 D hDH
  obtain ⟨y, hyA, hyD⟩ := exists_of_ssubset hDA
  have hxA : (x : X) ∈ A := mem_subtype.1 (hDA.subset hx)
  have hyA' : (y : X) ∈ A := mem_subtype.1 hyA
  obtain ⟨B, hB, hxB⟩ := hH.exists_mem_childClusters (one_lt_card.2 ⟨x, hxA, y, hyA', fun h => hyD (Subtype.ext h ▸ hx)⟩) hxA
  have hBS : (B ∩ S).Nonempty := ⟨x, mem_inter.2 ⟨hxB, x.2⟩⟩
  refine ⟨B, hB, hBS, ?_⟩
  by_contra hne
  exact Finset.disjoint_left.1 (hH'.disjoint_of_mem_childClusters (marg_subtype_mem_childClusters hH hA hB hBS (hbot B hB)) hD hne)
    (mem_subtype.2 hxB) hx

/-- A child `B` of `A` whose trace differs from that of `A` is the largest cluster with its
trace. -/
private theorem marg_filter_top (hH : IsHierarchy H) (hA : A ∈ H) (hB : B ∈ childClusters H A) (hBS : (B ∩ S).Nonempty)
    (hne : B.trace S ≠ A.trace S) :
    H.filter (fun A' => A' ≠ univ ∧ A'.trace S = B.trace S) =
      branchChain H S B := by
  obtain ⟨x, hx⟩ := subtype_nonempty_iff.2 hBS
  have := hH.2.2.2
  ext C
  simp only [mem_filter]
  grind [mem_childClusters, Finset.subtype_mono, ← (@Finset.mem_subtype X (Membership.mem S) _), disjoint_left]

/-- Along a chain of clusters with the same trace, the lengths add up. -/
private theorem marg_filter_chain (hH : IsHierarchy H) (hB₀ : B₀ ∈ childClusters H A) (htr : B₀.trace S = A.trace S)
    (hAS : (A ∩ S).Nonempty) (hA : A ∈ H) :
    branchChain H S A =
      insert A (branchChain H S B₀) := by
  obtain ⟨x, hx⟩ := subtype_nonempty_iff.2 hAS
  have := hH.2.2.2
  ext C
  simp only [mem_filter, mem_insert]
  grind [mem_childClusters, disjoint_left]

/-- At the bottom of a chain of clusters with the same trace, only the cluster itself counts. -/
private theorem marg_filter_bot (hA : A ∈ H) (hbot : ∀ B ∈ childClusters H A, B.trace S ≠ A.trace S) :
    branchChain H S A = {A} := by
  ext C
  simp only [mem_filter, mem_singleton]
  grind [IsHierarchy.exists_mem_childClusters_superset (H := H) (A := A),
    mem_childClusters, Finset.subtype_mono]

/-- A population from which no lineage is sampled produces the empty forest. -/
private theorem forestDist_eq_sum_entering_eq_empty (hH : IsHierarchy H)
    (len : Finset X → ℝ) {s : L → X} (hs : ∀ l, s l ∉ B)
    (G : Family L) : forestDist H len s B G = if G = ∅ then 1 else 0 := by
  have hz : ∀ G : Family L, G ≠ ∅ → forestDist H len s B G = 0 := by
    intro G hG
    by_contra h
    have := forestDist_support hH len s h
    simp only [clusterPreimage, hs, filter_false] at this
    grind [IsForest, → subset_lineages]
  have he := (sum_eq_single ∅ (fun G _ => hz G) (by simp)).symm.trans
    (forestDist_sum hH len s (A := B))
  split_ifs <;> grind

variable (hS : S.Nonempty) (s : L → S)
local notation "σS" => σ.restrict S hS

/-- Pruning, below the root: the forest leaving a cluster `A ≠ univ` meeting `S` is the forest
entering the trace of `A` in the induced tree, evolved for the lengths of the clusters below `A`
with the same trace. -/
private theorem marg_prune
    (hA : A ∈ σ.clusters) (hAS : (A ∩ S).Nonempty) :
    forestDist σ.clusters σ.length (Subtype.val ∘ s) A =
      enteringDist (σS).clusters (σS).length s (A.trace S) ᵥ*
        populationKernel (fun B => ∑ A' ∈ branchChain σ.clusters S B, σ.length A') A := by
  have hH := σ.isHierarchy
  induction A using Finset.strongInduction with
  | H A ih =>
  rw [forestDist_eq_sum_entering]
  by_cases hc : ∃ B₀ ∈ childClusters σ.clusters A, B₀.trace S = A.trace S
  · obtain ⟨B₀, hB₀, htr⟩ := hc
    obtain ⟨hB₀H, hB₀A, -⟩ := mem_childClusters.1 hB₀
    have he : enteringDist σ.clusters σ.length (Subtype.val ∘ s) A =
        forestDist σ.clusters σ.length (Subtype.val ∘ s) B₀ := by
      let r := Subtype.val ∘ s
      funext F
      have hmem (l) : r l ∈ A ↔ r l ∈ B₀ := by
        simpa only [r, Function.comp_apply, mem_subtype] using (Finset.ext_iff.1 htr (s l)).symm
      let b₀ : childClusters σ.clusters A := ⟨B₀, hB₀⟩
      unfold enteringDist
      rw [marg_sum_pi_restrict (· = b₀)
        (fun B => forestDist σ.clusters σ.length r B)
        (fun B hne G => forestDist_eq_sum_entering_eq_empty hH σ.length
          (fun l hl => Finset.disjoint_left.1
            (hH.disjoint_of_mem_childClusters B.2 hB₀ (fun h => hne (Subtype.ext h))) hl
            ((hmem l).1 ((mem_childClusters.1 B.2).2.1.subset hl))) G)]
      letI := Subtype.fintype (· = b₀)
      erw [← (Equiv.funUnique {B // B = b₀} (Family L)).symm.sum_comp]
      simp [Equiv.funUnique_symm_apply, Finset.univ_unique]
      trans ∑ F₀, if F₀ = F then forestDist σ.clusters σ.length r B₀ F₀ else 0
      · grind [→ forestDist_support, mem_sampledForest]
      · simp [r]
    rw [he,
      ih B₀ hB₀A hB₀H (subtype_nonempty_iff.1 (htr ▸ subtype_nonempty_iff.2 hAS))]
    simp only [populationKernel, if_neg (show B₀ ≠ univ from ne_top_of_lt hB₀A)]
    rw [htr, Matrix.vecMul_vecMul]
    by_cases hAu : A = univ
    · subst A
      simp only [ite_true]
      funext G
      apply sum_congr rfl
      intro F _
      dsimp only
      by_cases h0 : enteringDist (σS).clusters (σS).length s ((univ : Finset X).trace S) F = 0
      · simp only [h0, zero_mul]
      · congr 1
        exact kingmanTransition_mul_kingmanAbsorption
          (enteringDist_support (σS).isHierarchy _ s h0).1 _ G
    · simp only [if_neg hAu]
      rw [marg_filter_chain hH hB₀ htr hAS hA,
        sum_insert (fun h => not_subset_of_ssubset hB₀A (mem_filter.1 h).2.1), ← kingmanTransition_add, add_comm]
  · push Not at hc
    have he : enteringDist σ.clusters σ.length (Subtype.val ∘ s) A =
        enteringDist (σS).clusters (σS).length s (A.trace S) := by
      change _ = enteringDist (restrictClusters S σ.clusters) (σS).length s (A.trace S)
      funext F
      have hH' : IsHierarchy (restrictClusters S σ.clusters) := (σS).isHierarchy
      unfold enteringDist
      simp only [sampledForest, Function.comp_apply, mem_subtype]
      let e := Equiv.ofBijective
        (fun B : {B : childClusters σ.clusters A // (B.1 ∩ S).Nonempty} =>
          (⟨B.1.1.trace S,
            marg_subtype_mem_childClusters hH hA B.1.2 B.2 (hc _ B.1.2)⟩ :
              childClusters (restrictClusters S σ.clusters) (A.trace S)))
        ⟨fun B C h => Subtype.ext (Subtype.ext
            (by
              have := subtype_nonempty_iff.2 B.2
              have := congrArg Subtype.val h
              grind [→ IsHierarchy.disjoint_of_mem_childClusters, disjoint_left])),
          fun D => by
            obtain ⟨B, hB, hBS, hBD⟩ := marg_exists_child hH hH' hA hc D.2
            exact ⟨⟨⟨B, hB⟩, hBS⟩, Subtype.ext hBD⟩⟩
      rw [marg_sum_pi_restrict (fun B : childClusters σ.clusters A => (B.1 ∩ S).Nonempty)
        (fun B => forestDist σ.clusters σ.length (Subtype.val ∘ s) B)
        (fun B hBS G => forestDist_eq_sum_entering_eq_empty hH σ.length
          (fun l hl => hBS ⟨s l, mem_inter.2 ⟨hl, (s l).2⟩⟩) G)]
      erw [← (e.arrowCongr (Equiv.refl (Family L))).sum_comp]
      refine sum_congr rfl fun g _ => ?_
      dsimp only [Equiv.arrowCongr, Equiv.refl, Equiv.coe_fn_mk, Function.comp_def, id_eq]
      erw [sup_univ_equiv e.symm, ← e.prod_comp]
      simp only [Equiv.symm_apply_apply]
      congr 1
      apply prod_congr rfl
      rintro ⟨⟨B, hB⟩, hBS⟩ _
      apply congrFun
      change forestDist σ.clusters σ.length (Subtype.val ∘ s) B =
        forestDist (σS).clusters (σS).length s (B.trace S)
      have hBu : B.trace S ≠ univ := ne_top_of_lt (mem_childClusters.1 (marg_subtype_mem_childClusters hH hA hB hBS (hc B hB))).2.1
      have hlen : (σS).length (B.trace S) =
          ∑ A' ∈ branchChain σ.clusters S B, σ.length A' := by
        show σ.restrictLength S _ = _
        unfold SpeciesTree.restrictLength
        rw [marg_filter_top hH hA hB hBS (hc B hB)]
      rw [ih B (mem_childClusters.1 hB).2.1 (mem_childClusters.1 hB).1 hBS, forestDist_eq_sum_entering]
      unfold populationKernel
      rw [ite_eq_right (show B ≠ univ from ne_top_of_lt (mem_childClusters.1 hB).2.1), ite_eq_right hBu, hlen]
    rw [he]
    simp [populationKernel, marg_filter_bot hA hc]

variable (S)

/-- Pruning the species tree preserves its coalescent distribution. -/
theorem SpeciesTree.rootedDist_restrict (G : Family L) :
    (σS).rootedDist s G = σ.rootedDist (Subtype.val ∘ s) G := by
  unfold SpeciesTree.rootedDist
  rw [marg_prune σ hS s σ.univ_mem (by simpa using hS)]
  simp [forestDist_eq_sum_entering, populationKernel]

/-! ### Unrooting -/

/-- Lemma 5: restriction of the unrooted gene-tree distribution. -/
theorem lemma5 (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) (T' : Family S) :
    (σ.restrict S hS).unrootedDist id T' =
      ∑ T, if restrictSplits S T = T' then σ.unrootedDist id T else 0 := by
  unfold SpeciesTree.unrootedDist
  simp_rw [SpeciesTree.rootedDist_restrict]
  unfold SpeciesTree.rootedDist
  have hf (G : Family S) := forestDist_comp_subset (A := univ) σ.isHierarchy σ.length id S G
  simp only [Function.comp_def, Function.id_def] at hf ⊢
  simp_rw [hf]
  rw [marg_sum_ite_comp (restrictClusters S) unroot _ T',
    marg_sum_ite_comp unroot (restrictSplits S) _ T']
  simp_rw [unroot_restrictClusters]

theorem unrootedDist_restrict_eq {σ σ' : SpeciesTree X}
    (h : σ.unrootedDist id = σ'.unrootedDist id) (S : Finset X) (hS : S.Nonempty) :
    (σ.restrict S hS).unrootedDist id = (σ'.restrict S hS).unrootedDist id := by
  funext T'
  rw [lemma5, lemma5, h]

end ADR11
