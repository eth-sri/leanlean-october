module

public import ADR11.Coalescent.Outcome

/-!
# Basic properties of the multispecies coalescent

The recursion `ADR11.forestDist` is defined for any family of clusters `H` and any lengths; most
results here assume `H` is a hierarchy (`IsHierarchy H`) and the lengths are nonnegative.

* `enteringDist H len s A`: the distribution of the forest entering the population above `A`.
* `unrootedDistOf H len s`: the distribution of unrooted gene trees, for raw data; it is
  `SpeciesTree.unrootedDist` for a species tree.

## Main results

* `forestDist_eq_sum_entering`: `forestDist` is the entering distribution pushed through the
  population kernel.
* `forestDist_of_childClusters_eq_empty`, `forestDist_of_childClusters_eq_pair`: unfolding at a
  leaf and at a node with two children.
* `forestDist_singleton_of_card_le_one`, `forestDist_id_singleton`: at a leaf from which at most
  one lineage is sampled, the leaving forest is the sampled forest.
* `IsHierarchy.disjoint_of_mem_childClusters`, `IsHierarchy.exists_mem_childClusters`,
  `IsHierarchy.two_le_card_childClusters`: the children of a cluster with at least two elements
  partition it; `IsHierarchy.childClusters_eq_pair`: two disjoint clusters with union `A` are the
  children of `A`.
* `forestDist_support`: the forest leaving the population above `A` is a forest on exactly the
  lineages sampled from `A`, containing their singletons (`enteringDist_support`: the same for the
  entering forest).
* `forestDist_nonneg_of_ne_univ`, `forestDist_sum`, `unrootedDistOf_nonneg`,
  `unrootedDistOf_sum`: probability distributions.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] {L : Type*} [Fintype L] [DecidableEq L]

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

/-- The distribution of unrooted gene trees for raw data `H`, `len`. -/
noncomputable def unrootedDistOf (H : Finset (Finset X)) (len : Finset X → ℝ) (s : L → X)
    (T : Finset (Finset L)) : ℝ :=
  ∑ G, if unroot G = T then forestDist H len s univ G else 0

theorem SpeciesTree.unrootedDist_eq_unrootedDistOf (σ : SpeciesTree X) (s : L → X) :
    σ.unrootedDist s = unrootedDistOf σ.clusters σ.length s := rfl

theorem forestDist_eq_sum_entering (H : Finset (Finset X)) (len : Finset X → ℝ) (s : L → X)
    (A : Finset X) (G : Finset (Finset L)) :
    forestDist H len s A G = ∑ F, enteringDist H len s A F * populationKernel len A F G := by
  rw [forestDist]
  unfold enteringDist
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

theorem forestDist_of_childClusters_eq_empty {H : Finset (Finset X)} {len : Finset X → ℝ}
    {s : L → X} {A : Finset X} (h : childClusters H A = ∅) (G : Finset (Finset L)) :
    forestDist H len s A G = populationKernel len A (sampledForest s A) G := by
  rw [forestDist, h]; simp

/-- A sum over the functions on a two-element finset is a double sum. -/
lemma msc_sum_pi_pair {ι α β : Type*} [DecidableEq ι] [Fintype α] [AddCommMonoid β]
    {T : Finset ι} {B C : ι} (h : T = {B, C}) (hBC : B ≠ C) (g : (T → α) → β) :
    ∑ f : T → α, g f = ∑ a, ∑ b, g (fun D => if D.1 = B then a else b) := by
  subst h
  let e : (({B, C} : Finset ι) → α) ≃ α × α :=
    { toFun := fun f => (f ⟨B, by simp⟩, f ⟨C, by simp⟩)
      invFun := fun p D => if D.1 = B then p.1 else p.2
      left_inv := by
        intro f
        funext ⟨D, hD⟩
        grind
      right_inv := by
        intro p
        simp [hBC.symm] }
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  rfl

theorem forestDist_of_childClusters_eq_pair {H : Finset (Finset X)} {len : Finset X → ℝ}
    {s : L → X} {A B C : Finset X} (h : childClusters H A = {B, C}) (hBC : B ≠ C)
    (G : Finset (Finset L)) :
    forestDist H len s A G =
      ∑ F₁, ∑ F₂, forestDist H len s B F₁ * forestDist H len s C F₂ *
        populationKernel len A (F₁ ∪ F₂ ∪ sampledForest s A) G := by
  rw [forestDist, msc_sum_pi_pair h hBC]
  refine Finset.sum_congr rfl fun F₁ _ => Finset.sum_congr rfl fun F₂ _ => ?_
  congr 1
  · rw [Finset.prod_coe_sort (childClusters H A)
      (fun D => forestDist H len s D (if D = B then F₁ else F₂)), h, prod_pair hBC]
    simp [hBC.symm]
  · congr 2
    rw [univ_eq_attach, sup_attach (childClusters H A) (fun D => if D = B then F₁ else F₂), h,
      sup_insert, sup_singleton]
    simp [hBC.symm]

theorem mem_childClusters {H : Finset (Finset X)} {A B : Finset X} :
    B ∈ childClusters H A ↔ B ∈ H ∧ B ⊂ A ∧ ∀ C ∈ H, B ⊂ C → ¬ C ⊂ A :=
  mem_filter

/-- In a hierarchy, the children of a cluster with at least two elements partition it, and a
singleton has no children. -/
theorem IsHierarchy.childClusters_singleton {H : Finset (Finset X)} (hH : IsHierarchy H) (x : X) :
    childClusters H {x} = ∅ := by
  unfold childClusters
  rw [Finset.filter_eq_empty_iff]
  rintro B hB ⟨hBx, -⟩
  rw [Finset.ssubset_singleton_iff] at hBx
  subst hBx
  exact Finset.not_nonempty_empty (hH.2.2.1 _ hB)

/-- Two distinct children of a cluster of a hierarchy are disjoint. -/
theorem IsHierarchy.disjoint_of_mem_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A B C : Finset X} (hB : B ∈ childClusters H A) (hC : C ∈ childClusters H A) (hBC : B ≠ C) :
    Disjoint B C := by
  rw [mem_childClusters] at hB hC
  rcases hH.2.2.2 B hB.1 C hC.1 with h | h | h <;> grind

theorem mem_sampledForest {s : L → X} {A : Finset X} {C : Finset L} :
    C ∈ sampledForest s A ↔ ∃ l, s l ∈ A ∧ {l} = C := by
  simp [sampledForest]

theorem singleton_mem_sampledForest {s : L → X} {A : Finset X} {l : L} :
    {l} ∈ sampledForest s A ↔ s l ∈ A := by
  rw [mem_sampledForest]
  constructor
  · simp_all
  · grind

/-- The forest entering the population above a cluster `A` of a hierarchy, when the forests
leaving the children are forests on the lineages sampled from the children, is a forest on the
lineages sampled from `A`, containing their singletons. -/
theorem IsHierarchy.isForest_entering {H : Finset (Finset X)} (hH : IsHierarchy H) {s : L → X}
    {A : Finset X} (f : childClusters H A → Finset (Finset L))
    (hf : ∀ B, IsForest (f B) ∧ lineages (f B) = univ.filter (fun l => s l ∈ (B : Finset X))) :
    IsForest (univ.sup f ∪ sampledForest s A) ∧
      sampledForest s A ⊆ univ.sup f ∪ sampledForest s A ∧
      lineages (univ.sup f ∪ sampledForest s A) = univ.filter (fun l => s l ∈ A) := by
  have hsub := fun B C hC l hl =>
    (mem_filter.1 ((hf B).2 ▸ mem_lineages.2 ⟨C, hC, hl⟩ : l ∈ univ.filter _)).2
  refine ⟨⟨fun C hC => ?_, fun C hC D hD => ?_⟩, subset_union_right, ?_⟩
  · rcases mem_union.1 hC with hC | hC
    · obtain ⟨B, -, hCB⟩ := Finset.mem_sup.1 hC
      exact (hf B).1.1 C hCB
    · exact (isForest_sampledForest s A).1 C hC
  · rcases mem_union.1 hD with hD' | hD'
    · rcases mem_union.1 hC with hC' | hC'
      · obtain ⟨B, -, hCB⟩ := Finset.mem_sup.1 hC'
        obtain ⟨B', -, hDB'⟩ := Finset.mem_sup.1 hD'
        by_cases hBB' : B = B'
        · subst hBB'
          exact (hf B).1.2 C hCB D hDB'
        · exact Or.inr (Or.inr (Finset.disjoint_left.2 fun l hlC hlD => Finset.disjoint_left.1
            (hH.disjoint_of_mem_childClusters B.2 B'.2 (fun h => hBB' (Subtype.ext h)))
            (hsub B C hCB l hlC) (hsub B' D hDB' l hlD)))
      · obtain ⟨l, -, rfl⟩ := mem_sampledForest.1 hC'
        by_cases h : l ∈ D <;> simp [h]
    · obtain ⟨l, -, rfl⟩ := mem_sampledForest.1 hD'
      by_cases h : l ∈ C <;> simp [h]
  · ext l
    simp only [mem_lineages, mem_filter, mem_union, mem_univ, true_and]
    refine ⟨fun ⟨C, hC, hlC⟩ => hC.elim (fun hC => ?_) fun hC => ?_,
      fun h => ⟨{l}, Or.inr (singleton_mem_sampledForest.2 h), mem_singleton_self l⟩⟩
    · obtain ⟨B, -, hCB⟩ := Finset.mem_sup.1 hC
      exact (mem_childClusters.1 B.2).2.1.1 (hsub B C hCB l hlC)
    · obtain ⟨l', hl', rfl⟩ := mem_sampledForest.1 hC
      grind

/-- The population kernels only add clusters to a forest and keep its lineages. -/
theorem populationKernel_support {len : Finset X → ℝ} {A : Finset X} {F G : Finset (Finset L)}
    (hF : IsForest F) (h : populationKernel len A F G ≠ 0) :
    IsForest G ∧ F ⊆ G ∧ lineages G = lineages F := by
  unfold populationKernel at h
  split_ifs at h with hA
  · rw [kingmanAbsorption_apply hF] at h
    split_ifs at h with h0 h1 h2
    · grind
    · grind
    · obtain ⟨h1, h2, h3, -⟩ := jumpMatrix_pow_support hF h
      grind
    · grind
  · rw [kingmanTransition_apply hF] at h
    obtain ⟨h1, h2, h3, -⟩ := jumpMatrix_pow_support hF (right_ne_zero_of_mul h)
    grind

theorem populationKernel_nonneg {len : Finset X → ℝ} {A : Finset X} (hlen : A ≠ univ → 0 ≤ len A)
    {F : Finset (Finset L)} (hF : IsForest F) (G : Finset (Finset L)) :
    0 ≤ populationKernel len A F G := by
  unfold populationKernel
  split_ifs with hA
  · exact kingmanAbsorption_nonneg hF G
  · exact kingmanTransition_nonneg (hlen hA) F G

theorem populationKernel_sum (len : Finset X → ℝ) (A : Finset X) {F : Finset (Finset L)}
    (hF : IsForest F) : ∑ G, populationKernel len A F G = 1 := by
  unfold populationKernel
  split_ifs with hA
  · exact kingmanAbsorption_sum hF
  · exact kingmanTransition_sum hF (len A)

/-- The forest leaving the population above a cluster `A` of a hierarchy is a forest on exactly
the lineages sampled from `A`, containing the singletons of all of them. -/
theorem forestDist_support {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) {A : Finset X} (hA : A ∈ H) {G : Finset (Finset L)}
    (hG : forestDist H len s A G ≠ 0) :
    IsForest G ∧ sampledForest s A ⊆ G ∧ lineages G = univ.filter (fun l => s l ∈ A) := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist] at hG
  obtain ⟨f, -, hf⟩ := Finset.exists_ne_zero_of_sum_ne_zero hG
  have hfB : ∀ B : childClusters H A,
      IsForest (f B) ∧ lineages (f B) = univ.filter (fun l => s l ∈ (B : Finset X)) := by
    intro B
    have hBmem := mem_childClusters.1 B.2
    obtain ⟨h1, -, h3⟩ := ih B hBmem.2.1 hBmem.1 (Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hf) B (mem_univ _))
    grind
  obtain ⟨hF, hSF, hLF⟩ := hH.isForest_entering f hfB
  obtain ⟨hG1, hG2, hG3⟩ := populationKernel_support hF (right_ne_zero_of_mul hf)
  grind

theorem forestDist_entering {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) {A : Finset X} {f : childClusters H A → Finset (Finset L)}
    (hf : ∏ B : childClusters H A, forestDist H len s B (f B) ≠ 0) :
    IsForest (univ.sup f ∪ sampledForest s A) ∧
      sampledForest s A ⊆ univ.sup f ∪ sampledForest s A ∧
      lineages (univ.sup f ∪ sampledForest s A) = univ.filter (fun l => s l ∈ A) :=
  hH.isForest_entering f fun B => by
    obtain ⟨h1, -, h3⟩ := forestDist_support hH len s (mem_childClusters.1 B.2).1
      (prod_ne_zero_iff.1 hf B (mem_univ _))
    grind

/-- Nonnegativity, assuming only that the lengths of the edges below the root are nonnegative
(the length at `univ` is irrelevant). -/
theorem forestDist_nonneg_of_ne_univ {H : Finset (Finset X)} (hH : IsHierarchy H)
    {len : Finset X → ℝ} (hlen : ∀ A ∈ H, A ≠ univ → 0 ≤ len A) (s : L → X) {A : Finset X}
    (hA : A ∈ H) (G : Finset (Finset L)) : 0 ≤ forestDist H len s A G := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist]
  refine Finset.sum_nonneg fun f _ => ?_
  by_cases hprod : ∏ B : childClusters H A, forestDist H len s B (f B) = 0
  · simp_all
  · exact mul_nonneg (Finset.prod_nonneg fun B _ => ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1 _) (populationKernel_nonneg (hlen A hA) (forestDist_entering hH len s hprod).1 G)

theorem forestDist_sum {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) {A : Finset X} (hA : A ∈ H) : ∑ G, forestDist H len s A G = 1 := by
  induction A using Finset.strongInduction with
  | H A ih =>
  have hterm : ∀ f : childClusters H A → Finset (Finset L),
      (∏ B : childClusters H A, forestDist H len s B (f B)) *
        ∑ G, populationKernel len A (univ.sup f ∪ sampledForest s A) G =
      ∏ B : childClusters H A, forestDist H len s B (f B) := fun f => by
    by_cases hprod : ∏ B : childClusters H A, forestDist H len s B (f B) = 0
    · grind
    · rw [populationKernel_sum len A (forestDist_entering hH len s hprod).1, mul_one]
  conv_lhs => arg 2; ext G; rw [forestDist]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hterm]
  rw [← Fintype.prod_sum (fun (B : childClusters H A) (F : Finset (Finset L)) =>
    forestDist H len s B F)]
  exact Finset.prod_eq_one fun B _ =>
    ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1

/-! ### The entering distribution -/

/-- The forest entering the population above a cluster `A` of a hierarchy is a forest on exactly
the lineages sampled from `A`, containing the singletons of all of them. -/
theorem enteringDist_support {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) {A : Finset X} {F : Finset (Finset L)} (hF : enteringDist H len s A F ≠ 0) :
    IsForest F ∧ sampledForest s A ⊆ F ∧ lineages F = univ.filter (fun l => s l ∈ A) := by
  obtain ⟨f, -, hf⟩ := Finset.exists_ne_zero_of_sum_ne_zero hF
  split_ifs at hf with hfF
  · exact hfF ▸ forestDist_entering hH len s hf
  · grind

/-! ### The children of a cluster of a hierarchy -/

/-- Every element of a cluster `A` with at least two elements lies in a child of `A`. -/
theorem IsHierarchy.exists_mem_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A : Finset X} (hA : 2 ≤ #A) {x : X} (hx : x ∈ A) : ∃ B ∈ childClusters H A, x ∈ B := by
  have hxA : ({x} : Finset X) ⊂ A := by grind
  obtain ⟨B, hB, hmax⟩ := (H.filter fun C => x ∈ C ∧ C ⊂ A).exists_max_image card
    ⟨{x}, mem_filter.2 ⟨hH.2.1 x, mem_singleton_self x, hxA⟩⟩
  rw [mem_filter] at hB
  refine ⟨B, mem_childClusters.2 ⟨hB.1, hB.2.2, fun C hC hBC hCA => ?_⟩, hB.2.1⟩
  have := hmax C (mem_filter.2 ⟨hC, hBC.subset hB.2.1, hCA⟩)
  exact absurd (card_lt_card hBC) (not_lt.2 this)

/-- A cluster with at least two elements has at least two children. -/
theorem IsHierarchy.two_le_card_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A : Finset X} (hA : 2 ≤ #A) : 2 ≤ #(childClusters H A) := by
  by_contra hlt
  have hle : #(childClusters H A) ≤ 1 := by omega
  obtain ⟨x, hx⟩ : A.Nonempty := card_pos.1 (by omega)
  obtain ⟨B, hB, -⟩ := hH.exists_mem_childClusters hA hx
  rw [Finset.card_le_one_iff] at hle
  have hAB : A ⊆ B := fun y hy => by
    obtain ⟨C, hC, hyC⟩ := hH.exists_mem_childClusters hA hy
    grind
  exact not_subset_of_ssubset (mem_childClusters.1 hB).2.1 hAB

/-- Two disjoint clusters whose union is `A` are the children of `A`. -/
theorem IsHierarchy.childClusters_eq_pair {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A B C : Finset X} (hB : B ∈ H) (hC : C ∈ H) (hBC : Disjoint B C) (hA : B ∪ C = A) :
    childClusters H A = {B, C} := by
  subst hA
  have key {B C} (hB : B ∈ H) (hC : C ∈ H) (hBC : Disjoint B C) D (hD : D ∈ H) (hBD : B ⊆ D)
      (hDA : D ⊂ B ∪ C) : D = B := by
    rcases hH.2.2.2 D hD C hC with h | h | h
    · exact absurd (hBC.eq_bot_of_le (hBD.trans h)) (hH.2.2.1 B hB).ne_empty
    · grind
    · exact (h.left_le_of_le_sup_right hDA.subset).antisymm hBD
  have key' {B C} (hC : C ∈ H) (hBC : Disjoint B C) : B ⊂ B ∪ C :=
    subset_union_left.ssubset_of_ne fun h =>
      (hH.2.2.1 C hC).ne_empty (hBC.symm.eq_bot_of_le (subset_union_right.trans h.ge))
  have hmin {B C} (hB : B ∈ H) (hC : C ∈ H) (hBC : Disjoint B C) :
      B ∈ H ∧ B ⊂ B ∪ C ∧ ∀ D ∈ H, B ⊂ D → ¬D ⊂ B ∪ C :=
    ⟨hB, key' hC hBC, fun D hD hED hDA => hED.ne (key hB hC hBC D hD hED.subset hDA).symm⟩
  ext E
  simp [mem_childClusters, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hE, hEA, hmax⟩
    have hsub D (hD : D ∈ H) (hDA : D ⊂ B ∪ C) (hED : E ⊆ D) : E = D := by grind
    rcases hH.2.2.2 E hE B hB with h | h | h
    · simp_all <;> grind
    · simp_all <;> grind
    · rw [union_comm] at hsub
      exact Or.inr (hsub C hC (key' hB hBC.symm) (h.left_le_of_le_sup_left hEA.subset))
  · rintro (rfl | rfl)
    · grind
    · simp_all <;> grind

/-! ### Leaves -/

/-- At a leaf `{x}` from which at most one lineage is sampled, the forest leaving the population
is the sampled forest, whatever the length of the pendant edge. -/
theorem forestDist_singleton_of_card_le_one {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) {s : L → X} {x : X} (hx : #(univ.filter fun l => s l = x) ≤ 1)
    (G : Finset (Finset L)) :
    forestDist H len s {x} G = if G = sampledForest s {x} then 1 else 0 := by
  rw [forestDist_of_childClusters_eq_empty (hH.childClusters_singleton x)]
  have hF := isForest_sampledForest s ({x} : Finset X)
  have hk : #(roots (sampledForest s {x})) ≤ 1 := by
    refine (card_le_card (roots_subset _)).trans (card_image_le.trans ?_)
    simpa using hx
  by_cases hxu : ({x} : Finset X) = univ
  · rw [populationKernel, ite_eq_left hxu, kingmanAbsorption_apply hF]
    by_cases h0 : #(roots (sampledForest s {x})) = 0
    · grind
    · have h1 : #(roots (sampledForest s {x})) = 1 := by omega
      rw [ite_eq_right h0, h1, Nat.sub_self, pow_zero, Matrix.one_apply]
      by_cases hG : G = sampledForest s {x} <;> grind
  · rw [populationKernel, ite_eq_right hxu]
    exact kingmanTransition_of_card_roots_le_one hF hk _ G

/-- With one lineage per taxon, the forest leaving the population above a leaf `{x}` is the
single lineage `{x}`. -/
theorem forestDist_id_singleton {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) (x : X) (G : Finset (Finset X)) :
    forestDist H len id {x} G = if G = {{x}} then 1 else 0 := by
  have hS : sampledForest (id : X → X) {x} = {{x}} := by
    ext C
    simp [sampledForest, eq_comm]
  rw [forestDist_singleton_of_card_le_one hH len (by simp [Finset.filter_eq']) G, hS]

/-! ### Dependence on the lengths -/

/-! ### Species trees: probability distributions -/

theorem unrootedDistOf_nonneg {H : Finset (Finset X)} (hH : IsHierarchy H) {len : Finset X → ℝ}
    (hlen : ∀ A ∈ H, A ≠ univ → 0 ≤ len A) (s : L → X) (T : Finset (Finset L)) :
    0 ≤ unrootedDistOf H len s T := by
  refine Finset.sum_nonneg fun G _ => ?_
  split_ifs
  · exact forestDist_nonneg_of_ne_univ hH hlen s hH.1 G
  · grind

theorem unrootedDistOf_sum {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) : ∑ T, unrootedDistOf H len s T = 1 := by
  unfold unrootedDistOf
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq, mem_univ, ite_true]
  exact forestDist_sum hH len s hH.1

end ADR11
