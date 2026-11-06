module

public import ADR11.Trees.Hierarchy

/-!
# Marginalization

The paper's Lemma 5 is "clear from the structure of the coalescent model". It combines two facts:

* *Dropping lineages* (`forestDist_comp_embedding`): the forest formed by a subset of the lineages
  is distributed as the multispecies coalescent of that subset. Kingman's coalescent is
  consistent: restricting a forest to a subset of the lineages lumps the chain into Kingman's
  coalescent on the subset (`kingmanTransition_lump`, `kingmanAbsorption_lump`).
* *Pruning the species tree* (`rootedDist_restrict`): when only taxa in `S` are sampled, the
  populations without lineages do nothing, populations in a chain with the same lineages merge
  into one population whose length is the sum (`kingmanTransition_add`), and the populations above
  the most recent common ancestor of `S` merge into the population above the root.

* `restrictForest e F`: the restriction of a forest on `L` to the lineages `L'`, along an
  embedding `e : L' ↪ L`.
* `restrictUnrooted e T`: the restriction of an unrooted tree (given by the sides of its splits)
  to the lineages `L'`.

## Main results

* `kingmanTransition_lump`, `kingmanAbsorption_lump`: lumpability of Kingman's coalescent. The
  generators intertwine, `Q M = M Q'` on the rows of forests, where `M` is the restriction map:
  merging two roots that both meet the range of `e` merges their traces, and the other merges do
  not change the restriction.
* `forestDist_comp_embedding`, `SpeciesTree.rootedDist_comp_embedding`,
  `SpeciesTree.unrootedDist_comp_embedding`: dropping lineages.
* `SpeciesTree.rootedDist_restrict`: pruning the species tree. It is proved by strong induction
  on the clusters `A` meeting `S`: the forest leaving `A` is the forest entering the trace
  `A ∩ S` in `σ(S)`, evolved for the sum of the lengths of the clusters `A' ⊆ A` with the same
  trace (a chain).
* `unroot_restrictForest`: unrooting commutes with restricting (for any family of clusters).
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {L : Type*} [Fintype L] [DecidableEq L] {L' : Type*} [Fintype L'] [DecidableEq L']

/-- The restriction of a forest on `L` to the lineages `L'`, along an embedding `e : L' ↪ L`: the
nonempty traces of its clusters. -/
def restrictForest (e : L' ↪ L) (F : Finset (Finset L)) : Finset (Finset L') :=
  (F.filter fun A => ∃ l, e l ∈ A).image fun A => univ.filter fun l => e l ∈ A

/-! ### Restricting forests -/

theorem marg_mem_restrictForest (e : L' ↪ L) {F : Finset (Finset L)} {D : Finset L'} :
    D ∈ restrictForest e F ↔ ∃ A ∈ F, (∃ l, e l ∈ A) ∧ (univ.filter fun l => e l ∈ A) = D := by
  simp [restrictForest, and_assoc]

theorem marg_tr_mem_restrictForest (e : L' ↪ L) {F : Finset (Finset L)} {A : Finset L}
    (hA : A ∈ F) (hmeet : ∃ l, e l ∈ A) :
    (univ.filter fun l => e l ∈ A) ∈ restrictForest e F := by unfold restrictForest; grind

theorem marg_tr_mono (e : L' ↪ L) {A B : Finset L} (h : A ⊆ B) :
    (univ.filter fun l => e l ∈ A) ⊆ univ.filter fun l => e l ∈ B := by
  grind

theorem IsForest.restrictForest {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L) :
    IsForest (restrictForest e F) := by
  refine ⟨fun D hD => ?_, fun D hD D' hD' => ?_⟩
  · obtain ⟨A, -, ⟨l, hl⟩, rfl⟩ := (marg_mem_restrictForest e).1 hD
    exact ⟨l, by simpa⟩
  · obtain ⟨A, hA, -, rfl⟩ := (marg_mem_restrictForest e).1 hD
    obtain ⟨B, hB, -, rfl⟩ := (marg_mem_restrictForest e).1 hD'
    exact (hF.2 A hA B hB).imp (marg_tr_mono e) (Or.imp (marg_tr_mono e) fun h => disjoint_filter.2 fun l _ hA => disjoint_left.1 h hA)

theorem marg_restrictForest_insert (e : L' ↪ L) (C : Finset L) (F : Finset (Finset L)) :
    restrictForest e (insert C F) =
      if ∃ l, e l ∈ C then insert (univ.filter fun l => e l ∈ C) (restrictForest e F)
      else restrictForest e F := by aesop (add simp [restrictForest])

/-- The trace is injective on the roots meeting the range of `e`. -/
theorem marg_tr_inj {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L)
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) (hmeet : ∃ l, e l ∈ A)
    (h : (univ.filter fun l => e l ∈ A) = univ.filter fun l => e l ∈ B) : A = B := by
  obtain ⟨l, hl⟩ := hmeet
  have hlB : l ∈ univ.filter fun l => e l ∈ B := by grind
  exact hF.eq_of_mem_roots_of_mem hA hB hl (mem_filter.1 hlB).2

/-- The roots of the restriction of a forest are the traces of its roots meeting the range. -/
theorem marg_mem_roots_restrictForest {F : Finset (Finset L)} (hF : IsForest F)
    (e : L' ↪ L) {D : Finset L'} :
    D ∈ roots (restrictForest e F) ↔
      ∃ A ∈ roots F, (∃ l, e l ∈ A) ∧ (univ.filter fun l => e l ∈ A) = D := by
  constructor
  · intro hD
    obtain ⟨hDF, hmax⟩ := mem_roots.1 hD
    obtain ⟨A, hA, ⟨l, hl⟩, rfl⟩ := (marg_mem_restrictForest e).1 hDF
    obtain ⟨R, hR, hAR⟩ := exists_mem_roots_subset hA
    exact ⟨R, hR, ⟨l, hAR hl⟩, hmax _ (marg_tr_mem_restrictForest e (roots_subset F hR) ⟨l, hAR hl⟩)
      (marg_tr_mono e hAR)⟩
  · rintro ⟨A, hA, ⟨l, hl⟩, rfl⟩
    refine mem_roots.2 ⟨marg_tr_mem_restrictForest e (roots_subset F hA) ⟨l, hl⟩, fun D hD hAD => ?_⟩
    obtain ⟨B, hB, -, rfl⟩ := (marg_mem_restrictForest e).1 hD
    obtain ⟨R, hR, hBR⟩ := exists_mem_roots_subset hB
    obtain rfl := hF.eq_of_mem_roots_of_mem hA hR hl
      (hBR (mem_filter.1 (hAD (mem_filter.2 ⟨mem_univ l, hl⟩))).2)
    grind

/-- The restriction of a merge: merging two roots that both meet the range of `e` merges their
traces; otherwise the restriction does not change. -/
theorem marg_restrictForest_merge {F : Finset (Finset L)} (e : L' ↪ L)
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) :
    restrictForest e (insert (A ∪ B) F) =
      if (∃ l, e l ∈ A) ∧ (∃ l, e l ∈ B) then
        insert ((univ.filter fun l => e l ∈ A) ∪ univ.filter fun l => e l ∈ B)
          (restrictForest e F)
      else restrictForest e F := by
  have hr := fun C (hC : C ∈ roots F) (h : ∃ l, e l ∈ C) =>
    insert_eq_of_mem (marg_tr_mem_restrictForest e (roots_subset F hC) h)
  rw [marg_restrictForest_insert]
  by_cases hAm : ∀ l, e l ∉ A <;> by_cases hBm : ∀ l, e l ∉ B <;> (try push Not at hAm) <;>
    (try push Not at hBm) <;> simp [hAm, hBm, hr A hA, hr B hB, filter_or, exists_or]

/-- The merges of `F` whose restriction differs from the restriction of `F`: the merges of two
roots that both meet the range of `e`. -/
theorem marg_mem_merges_ne {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L)
    {H : Finset (Finset L)} :
    (H ∈ merges F ∧ restrictForest e H ≠ restrictForest e F) ↔
      ∃ A ∈ roots F, ∃ B ∈ roots F, A ≠ B ∧ (∃ l, e l ∈ A) ∧ (∃ l, e l ∈ B) ∧
        H = insert (A ∪ B) F := by
  constructor
  · rintro ⟨hH, hne⟩
    obtain ⟨A, hA, B, hB, hAB, rfl⟩ := mem_merges.1 hH
    rw [marg_restrictForest_merge e hA hB] at hne
    split_ifs at hne with h
    exacts [⟨A, hA, B, hB, hAB, h.1, h.2, rfl⟩, absurd rfl hne]
  · rintro ⟨A, hA, B, hB, hAB, hAm, hBm, rfl⟩
    refine ⟨mem_merges.2 ⟨A, hA, B, hB, hAB, rfl⟩, ?_⟩
    rw [marg_restrictForest_merge e hA hB, ite_eq_left ⟨hAm, hBm⟩]
    exact fun h => union_not_mem_of_mem_roots ((marg_mem_roots_restrictForest hF e).2 ⟨A, hA, hAm, rfl⟩)
      ((marg_mem_roots_restrictForest hF e).2 ⟨B, hB, hBm, rfl⟩)
      (fun h' => hAB (marg_tr_inj hF e hA hB hAm h')) (h ▸ mem_insert_self _ _)

/-- The key count behind lumpability: summing a function of the restriction over the merges of
`F` gives the sum over the merges of the restriction, plus the merges that do not change the
restriction. -/
theorem marg_sum_merges {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L)
    (u : Finset (Finset L') → ℝ) :
    -((#(roots F)).choose 2 : ℝ) * u (restrictForest e F) +
        ∑ H ∈ merges F, u (restrictForest e H) =
      -((#(roots (restrictForest e F))).choose 2 : ℝ) * u (restrictForest e F) +
        ∑ H' ∈ merges (restrictForest e F), u H' := by
  set rF := restrictForest e F
  have hrFf := hF.restrictForest e
  set M₂ := (merges F).filter fun H => restrictForest e H ≠ rF
  -- the restriction maps `M₂` onto the merges of `rF`
  have himage : M₂.image (restrictForest e) = merges rF := by
    ext H'
    rw [mem_image]
    constructor
    · rintro ⟨H, hH, rfl⟩
      obtain ⟨A, hA, B, hB, hAB, hAm, hBm, rfl⟩ :=
        (marg_mem_merges_ne hF e).1 (mem_filter.1 hH)
      rw [marg_restrictForest_merge e hA hB, ite_eq_left ⟨hAm, hBm⟩]
      exact mem_merges.2 ⟨_, (marg_mem_roots_restrictForest hF e).2 ⟨A, hA, hAm, rfl⟩, _,
        (marg_mem_roots_restrictForest hF e).2 ⟨B, hB, hBm, rfl⟩,
        fun h' => hAB (marg_tr_inj hF e hA hB hAm h'), rfl⟩
    · intro hH'
      obtain ⟨A', hA', B', hB', hAB', rfl⟩ := mem_merges.1 hH'
      obtain ⟨A, hA, hAm, rfl⟩ := (marg_mem_roots_restrictForest hF e).1 hA'
      obtain ⟨B, hB, hBm, rfl⟩ := (marg_mem_roots_restrictForest hF e).1 hB'
      refine ⟨insert (A ∪ B) F, mem_filter.2 ((marg_mem_merges_ne hF e).2
        ⟨A, hA, B, hB, fun h => hAB' (by rw [h]), hAm, hBm, rfl⟩), ?_⟩
      rw [marg_restrictForest_merge e hA hB, ite_eq_left ⟨hAm, hBm⟩]
  -- and is injective on `M₂`
  have hinj : Set.InjOn (restrictForest e) (M₂ : Set (Finset (Finset L))) := by
    intro H₁ hH₁ H₂ hH₂ h12
    obtain ⟨A₁, hA₁, B₁, hB₁, hAB₁, hA₁m, hB₁m, rfl⟩ :=
      (marg_mem_merges_ne hF e).1 (mem_filter.1 (mem_coe.1 hH₁))
    obtain ⟨A₂, hA₂, B₂, hB₂, hAB₂, hA₂m, hB₂m, rfl⟩ :=
      (marg_mem_merges_ne hF e).1 (mem_filter.1 (mem_coe.1 hH₂))
    rw [marg_restrictForest_merge e hA₁ hB₁, ite_eq_left ⟨hA₁m, hB₁m⟩,
      marg_restrictForest_merge e hA₂ hB₂, ite_eq_left ⟨hA₂m, hB₂m⟩] at h12
    have hr := fun {A} (hA : A ∈ roots F) (hAm : ∃ l, e l ∈ A) =>
      (marg_mem_roots_restrictForest hF e).2 ⟨A, hA, hAm, rfl⟩
    rcases Sym2.eq_iff.1 (hrFf.merge_inj (hr hA₁ hA₁m) (hr hB₁ hB₁m)
      (fun h => hAB₁ (marg_tr_inj hF e hA₁ hB₁ hA₁m h)) (hr hA₂ hA₂m) (hr hB₂ hB₂m)
      (fun h => hAB₂ (marg_tr_inj hF e hA₂ hB₂ hA₂m h)) h12) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [marg_tr_inj hF e hA₁ hA₂ hA₁m h1, marg_tr_inj hF e hB₁ hB₂ hB₁m h2]
    · rw [marg_tr_inj hF e hA₁ hB₂ hA₁m h1, marg_tr_inj hF e hB₁ hA₂ hB₁m h2, union_comm]
  rw [← hF.card_merges, ← hrFf.card_merges, ← himage, card_image_of_injOn hinj, sum_image hinj,
    ← card_filter_add_card_filter_not (s := merges F) (fun H => restrictForest e H = rF),
    ← sum_filter_add_sum_filter_not (merges F) (fun H => restrictForest e H = rF),
    sum_congr rfl fun H hH => by rw [(mem_filter.1 hH).2], sum_const, nsmul_eq_mul]
  push_cast
  ring

/-- Intertwining of the generators: `Q M = M Q'` on the rows of forests, tested against `w`. -/
theorem marg_sum_kingmanGenerator {F : Finset (Finset L)} (hF : IsForest F)
    (e : L' ↪ L) (w : Finset (Finset L') → ℝ) :
    ∑ G, kingmanGenerator F G * w (restrictForest e G) =
      ∑ G', kingmanGenerator (restrictForest e F) G' * w G' := by
  rw [hF.sum_kingmanGenerator_mul (fun G => w (restrictForest e G)),
    (hF.restrictForest e).sum_kingmanGenerator_mul w]
  exact marg_sum_merges hF e w

/-- The generator is supported on the forest itself and its merges. -/
theorem marg_kingmanGenerator_ne_zero {F G : Finset (Finset L)} (hF : IsForest F)
    (h : kingmanGenerator F G ≠ 0) : IsForest G := by
  rw [kingmanGenerator_apply_of_isForest] at h
  split_ifs at h with h1 h2
  · grind
  · exact (hF.of_mem_merges h2).1
  · grind

theorem marg_sum_kingmanGenerator_pow (e : L' ↪ L) (n : ℕ) {F : Finset (Finset L)}
    (hF : IsForest F) (w : Finset (Finset L') → ℝ) :
    ∑ G, (kingmanGenerator ^ n) F G * w (restrictForest e G) =
      ∑ G', (kingmanGenerator ^ n) (restrictForest e F) G' * w G' := by
  induction n generalizing F w with
  | zero => simp [Matrix.one_apply]
  | succ n ih =>
    simp_rw [pow_succ', Matrix.mul_apply, sum_mul, mul_assoc]
    rw [sum_comm, sum_comm (s := (univ : Finset (Finset (Finset L'))))]
    simp_rw [← mul_sum]
    rw [← marg_sum_kingmanGenerator hF e]
    refine sum_congr rfl fun H _ => ?_
    by_cases hQ : kingmanGenerator F H = 0
    · grind
    · rw [ih (marg_kingmanGenerator_ne_zero hF hQ)]

/-- Lumpability of Kingman's coalescent, tested against a function `w` of the restriction. -/
theorem marg_sum_kingmanTransition {F : Finset (Finset L)} (hF : IsForest F)
    (e : L' ↪ L) (t : ℝ) (w : Finset (Finset L') → ℝ) :
    ∑ G, kingmanTransition t F G * w (restrictForest e G) =
      ∑ G', kingmanTransition t (restrictForest e F) G' * w G' := by
  refine (hasSum_sum fun G _ => (hasSum_exp_apply (t • kingmanGenerator) F G).mul_right
    (w (restrictForest e G))).unique ?_
  convert hasSum_sum (s := univ) fun G' _ => (hasSum_exp_apply (t • kingmanGenerator)
    (restrictForest e F) G').mul_right (w G') using 1
  funext n
  simp_rw [smul_pow, Matrix.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum]
  rw [marg_sum_kingmanGenerator_pow e n hF w]
  rfl

/-- Consistency of Kingman's coalescent (lumpability). -/
theorem kingmanTransition_lump {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L) (t : ℝ)
    (G' : Finset (Finset L')) :
    ∑ G, (if restrictForest e G = G' then kingmanTransition t F G else 0) =
      kingmanTransition t (restrictForest e F) G' := by
  simpa using marg_sum_kingmanTransition hF e t fun G'' => if G'' = G' then 1 else 0

theorem kingmanAbsorption_lump {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L)
    (G' : Finset (Finset L')) :
    ∑ G, (if restrictForest e G = G' then kingmanAbsorption F G else 0) =
      kingmanAbsorption (restrictForest e F) G' := by
  refine tendsto_nhds_unique ?_ (tendsto_kingmanTransition (hF.restrictForest e) G')
  simp_rw [← kingmanTransition_lump hF e]
  exact tendsto_finsetSum _ fun G _ => by
    split_ifs; exacts [tendsto_kingmanTransition hF G, tendsto_const_nhds]

/-! ### Dropping lineages -/

theorem marg_restrictForest_union (e : L' ↪ L) (F₁ F₂ : Finset (Finset L)) :
    restrictForest e (F₁ ∪ F₂) = restrictForest e F₁ ∪ restrictForest e F₂ := by
  unfold restrictForest
  rw [filter_union, image_union]

theorem marg_restrictForest_sup {ι : Type*} (e : L' ↪ L) (T : Finset ι)
    (f : ι → Finset (Finset L)) :
    restrictForest e (T.sup f) = T.sup fun i => restrictForest e (f i) := by aesop (add simp [restrictForest])

theorem marg_restrictForest_sampledForest (e : L' ↪ L) (s : L → X) (A : Finset X) :
    restrictForest e (sampledForest s A) = sampledForest (s ∘ e) A := by
  ext D
  rw [marg_mem_restrictForest, mem_sampledForest]
  constructor
  · rintro ⟨_, hC, ⟨l', hl'⟩, rfl⟩
    obtain ⟨l, hl, rfl⟩ := mem_sampledForest.1 hC
    rw [mem_singleton] at hl'
    subst hl'
    refine ⟨l', hl, ?_⟩
    ext m
    simp
  · rintro ⟨l', hl', rfl⟩
    refine ⟨{e l'}, mem_sampledForest.2 ⟨e l', hl', rfl⟩, ⟨l', mem_singleton_self _⟩, ?_⟩
    ext m
    simp

/-- A sum of the form `∑ b, [g b = c] ∑ a, [f a = b] p a` is a pushforward. -/
theorem marg_sum_ite_comp {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [DecidableEq γ] (f : α → β) (g : β → γ) (p : α → ℝ) (c : γ) :
    ∑ b, (if g b = c then ∑ a, (if f a = b then p a else 0) else 0) =
      ∑ a, if g (f a) = c then p a else 0 := by
  rw [← sum_fiberwise univ f]
  exact sum_congr rfl fun b _ => by split_ifs with h <;> simp +contextual [sum_filter, h]

/-- The pushforward of a product is the product of the pushforwards. -/
theorem marg_prod_pushforward {ι : Type*} [Fintype ι] [DecidableEq ι] (e : L' ↪ L)
    (φ : ι → Finset (Finset L) → ℝ) (f' : ι → Finset (Finset L')) :
    ∏ i, (∑ F, if restrictForest e F = f' i then φ i F else 0) =
      ∑ f : ι → Finset (Finset L),
        if (fun i => restrictForest e (f i)) = f' then ∏ i, φ i (f i) else 0 := by
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun f _ => ?_
  rw [prod_ite_zero]
  simp [funext_iff]

theorem marg_populationKernel_lump (len : Finset X → ℝ) (A : Finset X)
    {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L) (G' : Finset (Finset L')) :
    ∑ G, (if restrictForest e G = G' then populationKernel len A F G else 0) =
      populationKernel len A (restrictForest e F) G' := by
  unfold populationKernel
  split_ifs
  · exact kingmanAbsorption_lump hF e G'
  · exact kingmanTransition_lump hF e _ G'

/-- Dropping lineages, for the forest entering a population. -/
theorem marg_enteringDist_comp_embedding {H : Finset (Finset X)} (len : Finset X → ℝ)
    (s : L → X) (e : L' ↪ L) {A : Finset X}
    (ih : ∀ B ∈ childClusters H A, ∀ G' : Finset (Finset L'), forestDist H len (s ∘ e) B G' =
      ∑ G, if restrictForest e G = G' then forestDist H len s B G else 0)
    (F' : Finset (Finset L')) :
    enteringDist H len (s ∘ e) A F' =
      ∑ F, if restrictForest e F = F' then enteringDist H len s A F else 0 := by
  unfold enteringDist
  rw [marg_sum_ite_comp (fun f : childClusters H A → Finset (Finset L) =>
      univ.sup f ∪ sampledForest s A) (restrictForest e)]
  have hP : ∀ f' : childClusters H A → Finset (Finset L'),
      ∏ B : childClusters H A, forestDist H len (s ∘ e) B (f' B) =
        ∑ f : childClusters H A → Finset (Finset L),
          if (fun B => restrictForest e (f B)) = f' then
            ∏ B : childClusters H A, forestDist H len s B (f B) else 0 := by
    intro f'
    rw [← marg_prod_pushforward e (fun B : childClusters H A => forestDist H len s B)]
    grind
  simp_rw [hP]
  rw [marg_sum_ite_comp (fun f : childClusters H A → Finset (Finset L) =>
      fun B => restrictForest e (f B)) (fun f' => univ.sup f' ∪ sampledForest (s ∘ e) A)]
  refine sum_congr rfl fun f _ => ?_
  rw [marg_restrictForest_union, marg_restrictForest_sup, marg_restrictForest_sampledForest]

/-- Dropping lineages: the multispecies coalescent of the lineages `L'` (sampled through
`s ∘ e`) is the restriction of the multispecies coalescent of the lineages `L`. -/
theorem forestDist_comp_embedding {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) (s : L → X) (e : L' ↪ L) {A : Finset X} (hA : A ∈ H)
    (G' : Finset (Finset L')) :
    forestDist H len (s ∘ e) A G' =
      ∑ G, if restrictForest e G = G' then forestDist H len s A G else 0 := by
  induction A using Finset.strongInduction generalizing G' with
  | H A ih =>
  have hent := marg_enteringDist_comp_embedding (H := H) len s e (A := A)
    (fun B hB G' => ih B (mem_childClusters.1 hB).2.1 (mem_childClusters.1 hB).1 G')
  calc forestDist H len (s ∘ e) A G'
      = ∑ F, enteringDist H len s A F * populationKernel len A (restrictForest e F) G' := by
        rw [forestDist_eq_sum_entering]
        simp_rw [hent, sum_mul, ite_mul, zero_mul]
        rw [sum_comm]
        simp
    _ = ∑ F, ∑ G, if restrictForest e G = G' then
          enteringDist H len s A F * populationKernel len A F G else 0 := sum_congr rfl fun F _ => by
        by_cases h0 : enteringDist H len s A F = 0
        · simp_all
        · simp_rw [← marg_populationKernel_lump len A (enteringDist_support hH len s h0).1 e G',
            mul_sum, mul_ite, mul_zero]
    _ = _ := by
        rw [sum_comm]
        exact sum_congr rfl fun G _ => by split_ifs <;> simp [forestDist_eq_sum_entering H len s A G]

theorem SpeciesTree.rootedDist_comp_embedding (σ : SpeciesTree X) (s : L → X) (e : L' ↪ L)
    (G' : Finset (Finset L')) :
    σ.rootedDist (s ∘ e) G' = ∑ G, if restrictForest e G = G' then σ.rootedDist s G else 0 :=
  forestDist_comp_embedding σ.isHierarchy σ.length s e σ.univ_mem G'

/-! ### Pruning the species tree -/

/-- Reindexing the sum defining the entering distribution: the children `i` with `¬ P i` always
produce the empty forest, and the others correspond bijectively, through `τ`, to the index set
`T'`. -/
theorem marg_sum_pi_reindex {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι']
    {T : Finset ι} {T' : Finset ι'} (P : ι → Prop) [DecidablePred P] (τ : ι → ι')
    (hmaps : ∀ i ∈ T, P i → τ i ∈ T')
    (hinj : ∀ i ∈ T, ∀ j ∈ T, P i → P j → τ i = τ j → i = j)
    (hsurj : ∀ i' ∈ T', ∃ i ∈ T, P i ∧ τ i = i')
    (φ : ι → Finset (Finset L) → ℝ) (ψ : ι' → Finset (Finset L) → ℝ)
    (h0 : ∀ i ∈ T, ¬ P i → ∀ F, φ i F = if F = ∅ then 1 else 0)
    (h1 : ∀ i ∈ T, P i → φ i = ψ (τ i)) (c F : Finset (Finset L)) :
    (∑ f : T → Finset (Finset L), if univ.sup f ∪ c = F then ∏ i : T, φ i (f i) else 0) =
      ∑ g : T' → Finset (Finset L), if univ.sup g ∪ c = F then ∏ i : T', ψ i (g i) else 0 := by
  choose j hjT hjP hjτ using hsurj
  -- `j` inverts `τ`
  have hji (i : T) (hP : P i) : (⟨j (τ i) (hmaps i i.2 hP), hjT _ _⟩ : T) = i := by grind
  have hij (i' : T') : (⟨τ (j i'.1 i'.2), hmaps _ (hjT _ _) (hjP _ _)⟩ : T') = i' := by grind
  -- only the functions vanishing outside `P` contribute
  rw [← sum_subset (filter_subset (fun f : T → _ => ∀ i : T, ¬ P i → f i = ∅) univ)
    fun f _ hf => ?_]
  · refine sum_nbij' (fun f i' => f ⟨j i'.1 i'.2, hjT _ _⟩)
      (fun g i => if h : P i then g ⟨τ i, hmaps i i.2 h⟩ else ∅)
      (fun _ _ => mem_univ _) (fun g _ => by simp +contextual) (fun f hf => ?_)
      (fun g _ => funext fun i' => by simp [hjP, hij]) (fun f hf => ?_)
    all_goals simp only [mem_filter, mem_univ, true_and] at hf
    · grind
    have hsup : univ.sup f = univ.sup fun i' : T' => f ⟨j i'.1 i'.2, hjT _ _⟩ := by
      refine le_antisymm (Finset.sup_le fun i _ => ?_) (Finset.sup_le fun i' _ => le_sup (f := f)
        (mem_univ _))
      by_cases hi : P i
      · exact (congrArg f (hji i hi)).ge.trans (le_sup (f := fun i' : T' => f ⟨j i'.1 i'.2,
          hjT _ _⟩) (mem_univ ⟨τ i, hmaps i i.2 hi⟩))
      · grind
    have hprod : ∏ i : T, φ i (f i) = ∏ i' : T', ψ i' (f ⟨j i'.1 i'.2, hjT _ _⟩) := by
      rw [← prod_filter_of_ne (p := fun i : T => P i) fun i _ hne => by_contra fun hi =>
        hne (by rw [h0 i i.2 hi, hf i hi, ite_eq_left rfl])]
      refine prod_bij' (fun i hi => ⟨τ i, hmaps i i.2 (mem_filter.1 hi).2⟩)
        (fun i' _ => ⟨j i'.1 i'.2, hjT _ _⟩) (fun _ _ => mem_univ _)
        (fun i' _ => mem_filter.2 ⟨mem_univ _, hjP _ _⟩) (fun i hi => hji i (mem_filter.1 hi).2)
        (fun i' _ => hij i') fun i hi => ?_
      rw [h1 i i.2 (mem_filter.1 hi).2, hji i (mem_filter.1 hi).2]
    rw [hsup, hprod]
  · simp only [mem_filter, mem_univ, true_and, not_forall] at hf
    obtain ⟨i, hPi, hfi⟩ := hf
    rw [prod_eq_zero (mem_univ i) (by rw [h0 i i.2 hPi, ite_eq_right hfi]), ite_self]

/-- The trace of a child of `A` meeting `S`, with a trace different from that of `A`, is a child
of the trace of `A` in the induced tree. -/
theorem marg_subtype_mem_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {S A B : Finset X} (hA : A ∈ H) (hB : B ∈ childClusters H A) (hBS : (B ∩ S).Nonempty)
    (hne : B.subtype (· ∈ S) ≠ A.subtype (· ∈ S)) :
    B.subtype (· ∈ S) ∈ childClusters (restrictClusters S H) (A.subtype (· ∈ S)) := by
  obtain ⟨hBH, hBA, hBmax⟩ := mem_childClusters.1 hB
  refine mem_childClusters.2 ⟨mem_restrictClusters.2 ⟨B, hBH, hBS, rfl⟩,
    (subtype_mono hBA.subset).ssubset_of_ne hne, fun E' hE' hBE' hE'A => ?_⟩
  obtain ⟨E, hE, -, rfl⟩ := mem_restrictClusters.1 hE'
  obtain ⟨x, hx⟩ := subtype_nonempty_iff.2 hBS
  have hxB := mem_subtype.1 hx
  have hxE := mem_subtype.1 (hBE'.subset hx)
  rcases hH.subset_or_subset_of_mem hE hA hxE (hBA.subset hxB) <;> rcases hH.subset_or_subset_of_mem hE hBH hxE hxB <;> grind

/-- Two children of a cluster meeting `S` with the same trace are equal. -/
theorem marg_eq_of_subtype_eq {H : Finset (Finset X)} (hH : IsHierarchy H)
    {S A B₁ B₂ : Finset X} (hB₁ : B₁ ∈ childClusters H A) (hB₂ : B₂ ∈ childClusters H A)
    (hB₁S : (B₁ ∩ S).Nonempty) (h : B₁.subtype (· ∈ S) = B₂.subtype (· ∈ S)) : B₁ = B₂ := by
  by_contra hne
  obtain ⟨x, hx⟩ := subtype_nonempty_iff.2 hB₁S
  exact disjoint_left.1 (hH.disjoint_of_mem_childClusters hB₁ hB₂ hne)
    (mem_subtype.1 hx) (mem_subtype.1 (h ▸ hx))

/-- If no child of `A` has the trace of `A`, every child of the trace of `A` in the induced tree
is the trace of a child of `A`. -/
theorem marg_exists_child {H : Finset (Finset X)} (hH : IsHierarchy H) {S A : Finset X}
    (hH' : IsHierarchy (restrictClusters S H)) (hA : A ∈ H)
    (hbot : ∀ B ∈ childClusters H A, B.subtype (· ∈ S) ≠ A.subtype (· ∈ S))
    {D : Finset S} (hD : D ∈ childClusters (restrictClusters S H) (A.subtype (· ∈ S))) :
    ∃ B ∈ childClusters H A, (B ∩ S).Nonempty ∧ B.subtype (· ∈ S) = D := by
  obtain ⟨hDH, hDA, -⟩ := mem_childClusters.1 hD
  obtain ⟨x, hx⟩ := hH'.2.2.1 D hDH
  obtain ⟨y, hyA, hyD⟩ := exists_of_ssubset hDA
  have hxA := mem_subtype.1 (hDA.subset hx)
  obtain ⟨B, hB, hxB⟩ := hH.exists_mem_childClusters
    (one_lt_card.2 ⟨x, hxA, y, mem_subtype.1 hyA, fun h => hyD (Subtype.ext h ▸ hx)⟩) hxA
  have hBS : (B ∩ S).Nonempty := ⟨x, mem_inter.2 ⟨hxB, x.2⟩⟩
  refine ⟨B, hB, hBS, by_contra fun hne => disjoint_left.1 (hH'.disjoint_of_mem_childClusters
    (marg_subtype_mem_childClusters hH hA hB hBS (hbot B hB)) hD hne) (mem_subtype.2 hxB) hx⟩

/-- A child `B` of `A` whose trace differs from that of `A` is the largest cluster with its
trace. -/
theorem marg_filter_top {H : Finset (Finset X)} (hH : IsHierarchy H) {S A B : Finset X}
    (hA : A ∈ H) (hB : B ∈ childClusters H A) (hBS : (B ∩ S).Nonempty)
    (hne : B.subtype (· ∈ S) ≠ A.subtype (· ∈ S)) :
    H.filter (fun A' => A' ≠ univ ∧ A'.subtype (· ∈ S) = B.subtype (· ∈ S)) =
      H.filter (fun A' => A' ⊆ B ∧ A'.subtype (· ∈ S) = B.subtype (· ∈ S)) := by
  obtain ⟨hBH, hBA, hBmax⟩ := mem_childClusters.1 hB
  ext A'
  simp only [mem_filter]
  refine ⟨fun ⟨hA'H, _, htr⟩ => ⟨hA'H, ?_, htr⟩, fun ⟨hA'H, hA'B, htr⟩ => ⟨hA'H, ?_, htr⟩⟩
  · obtain ⟨x, hx⟩ := subtype_nonempty_iff.2 hBS
    have hxB := mem_subtype.1 hx
    have hxA' := mem_subtype.1 (htr.symm ▸ hx : x ∈ A'.subtype (· ∈ S))
    rcases hH.subset_or_subset_of_mem hA'H hBH hxA' hxB with h | hBA'
    · grind
    rcases hBA'.eq_or_ssubset with rfl | hBA'
    · grind
    rcases hH.subset_or_subset_of_mem hA'H hA hxA' (hBA.subset hxB) with hA'A | hAA' <;> grind
  · grind

/-- Along a chain of clusters with the same trace, the lengths add up. -/
theorem marg_filter_chain {H : Finset (Finset X)} (hH : IsHierarchy H) {S A B₀ : Finset X}
    (hB₀ : B₀ ∈ childClusters H A) (htr : B₀.subtype (· ∈ S) = A.subtype (· ∈ S))
    (hAS : (A ∩ S).Nonempty) (hA : A ∈ H) :
    H.filter (fun A' => A' ⊆ A ∧ A'.subtype (· ∈ S) = A.subtype (· ∈ S)) =
      insert A (H.filter (fun A' => A' ⊆ B₀ ∧ A'.subtype (· ∈ S) = B₀.subtype (· ∈ S))) := by
  obtain ⟨hB₀H, hB₀A, -⟩ := mem_childClusters.1 hB₀
  ext A'
  simp
  refine ⟨fun ⟨hA'H, hA'A, htr'⟩ => hA'A.eq_or_ssubset.imp id fun hA'A =>
    ⟨hA'H, ?_, htr'.trans htr.symm⟩, ?_⟩
  · obtain ⟨B, hB, hA'B⟩ := hH.exists_mem_childClusters_superset hA'H hA'A
    obtain ⟨x, hx⟩ := subtype_nonempty_iff.2 hAS
    obtain rfl : B = B₀ := by_contra fun hne => disjoint_left.1
      (hH.disjoint_of_mem_childClusters hB hB₀ hne) (hA'B (mem_subtype.1 (htr'.symm ▸ hx)))
      (mem_subtype.1 (htr.symm ▸ hx))
    grind
  · grind

/-- At the bottom of a chain of clusters with the same trace, only the cluster itself counts. -/
theorem marg_filter_bot {H : Finset (Finset X)} (hH : IsHierarchy H) {S A : Finset X}
    (hA : A ∈ H) (hbot : ∀ B ∈ childClusters H A, B.subtype (· ∈ S) ≠ A.subtype (· ∈ S)) :
    H.filter (fun A' => A' ⊆ A ∧ A'.subtype (· ∈ S) = A.subtype (· ∈ S)) = {A} := by
  ext A'
  simp
  refine ⟨fun ⟨hA'H, hA'A, htr'⟩ => by_contra fun hne => ?_, by rintro rfl; exact ⟨hA, subset_rfl, rfl⟩⟩
  obtain ⟨B, hB, hA'B⟩ := hH.exists_mem_childClusters_superset hA'H (hA'A.ssubset_of_ne hne)
  exact hbot B hB (subset_antisymm (subtype_mono (mem_childClusters.1 hB).2.1.subset)
    (htr' ▸ subtype_mono hA'B))

/-- A population from which no lineage is sampled produces the empty forest. -/
theorem marg_forestDist_eq_empty {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) {s : L → X} {B : Finset X} (hB : B ∈ H) (hs : ∀ l, s l ∉ B)
    (G : Finset (Finset L)) : forestDist H len s B G = if G = ∅ then 1 else 0 := by
  have hz : ∀ G : Finset (Finset L), G ≠ ∅ → forestDist H len s B G = 0 := fun G hG => by_contra fun h => by
    obtain ⟨hGf, -, hlin⟩ := forestDist_support hH len s hB h
    obtain ⟨C, hC⟩ := nonempty_iff_ne_empty.2 hG
    obtain ⟨l, hl⟩ := hGf.1 C hC
    simpa [hlin, hs] using subset_lineages hC hl
  split_ifs with hG
  · rw [← forestDist_sum hH len s hB, hG, sum_eq_single ∅ (fun G _ => hz G) (by simp)]
  · grind

/-- At a cluster `A` with a child `B₀` with the same trace, the forest entering `A` is the forest
leaving `B₀`. -/
theorem marg_enteringDist_chain {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) {S : Finset X} {s : L → X} (hs : ∀ l, s l ∈ S) {A B₀ : Finset X}
    (hB₀ : B₀ ∈ childClusters H A) (htr : B₀.subtype (· ∈ S) = A.subtype (· ∈ S))
    (F : Finset (Finset L)) : enteringDist H len s A F = forestDist H len s B₀ F := by
  have hAB (l) (h : s l ∈ A) : s l ∈ B₀ :=
    mem_subtype.1 (htr ▸ mem_subtype.2 h : (⟨s l, hs l⟩ : S) ∈ B₀.subtype (· ∈ S))
  -- the other children receive no lineage
  have hother (B) (hB : B ∈ childClusters H A) (hne : B ≠ B₀) (l) (hl : s l ∈ B) : False :=
    disjoint_left.1 (hH.disjoint_of_mem_childClusters hB hB₀ hne) hl
      (hAB l ((mem_childClusters.1 hB).2.1.subset hl))
  have hSF : sampledForest s A = sampledForest s B₀ := by
    unfold sampledForest
    congr 1
    ext l
    simpa using ⟨hAB l, fun h => ((mem_childClusters.1 hB₀).2.1).subset h⟩
  unfold enteringDist
  rw [marg_sum_pi_reindex (T' := ({B₀} : Finset (Finset X))) (fun B => B = B₀) id
    (fun B _ h => h ▸ mem_singleton_self _) (fun B _ B' _ h h' _ => h.trans h'.symm)
    (fun i' hi' => ⟨B₀, hB₀, rfl, (mem_singleton.1 hi').symm⟩)
    (fun B => forestDist H len s B) (fun B => forestDist H len s B)
    (fun B hB hne F => marg_forestDist_eq_empty hH len (mem_childClusters.1 hB).1
      (hother B hB hne) F) (fun _ _ _ => rfl)]
  rw [← (Equiv.funUnique _ _).symm.sum_comp, hSF]
  have key (x : Finset (Finset L)) : (if x ∪ sampledForest s B₀ = F then
      forestDist H len s B₀ x else 0) = if x = F then forestDist H len s B₀ x else 0 := by
    by_cases h0 : forestDist H len s B₀ x = 0
    · grind
    · rw [union_eq_left.2 (forestDist_support hH len s (mem_childClusters.1 hB₀).1 h0).2.1]
  simp [key]

/-- The sum of the lengths of the clusters below `A` with the same trace as `A`. -/
noncomputable def marg_len (σ : SpeciesTree X) (S A : Finset X) : ℝ :=
  ∑ A' ∈ σ.clusters with A' ⊆ A ∧ A'.subtype (· ∈ S) = A.subtype (· ∈ S), σ.length A'

/-- At the bottom of a chain of clusters with the same trace, the forest entering `A` is the
forest entering its trace in the induced tree. -/
theorem marg_enteringDist_restrict (σ : SpeciesTree X) {S : Finset X} (hS : S.Nonempty)
    (s : L → S) {A : Finset X} (hA : A ∈ σ.clusters)
    (hbot : ∀ B ∈ childClusters σ.clusters A, B.subtype (· ∈ S) ≠ A.subtype (· ∈ S))
    (ih : ∀ B ∈ childClusters σ.clusters A, (B ∩ S).Nonempty → ∀ G,
      forestDist σ.clusters σ.length (fun l => (s l : X)) B G =
        ∑ F, enteringDist (σ.restrict S hS).clusters (σ.restrict S hS).length s
            (B.subtype (· ∈ S)) F * populationKernel (marg_len σ S) B F G)
    (F : Finset (Finset L)) :
    enteringDist σ.clusters σ.length (fun l => (s l : X)) A F =
      enteringDist (σ.restrict S hS).clusters (σ.restrict S hS).length s
        (A.subtype (· ∈ S)) F := by
  have hH := σ.isHierarchy
  have hSF : sampledForest (fun l => (s l : X)) A = sampledForest s (A.subtype (· ∈ S)) := by
    unfold sampledForest
    ext l
    simp
  unfold enteringDist
  rw [hSF]
  refine marg_sum_pi_reindex (fun B => (B ∩ S).Nonempty) (fun B => B.subtype (· ∈ S))
    (fun B hB hBS => marg_subtype_mem_childClusters hH hA hB hBS (hbot B hB))
    (fun B₁ hB₁ B₂ hB₂ hB₁S _ h => marg_eq_of_subtype_eq hH hB₁ hB₂ hB₁S h)
    (fun D hD => marg_exists_child hH ((σ.restrict S hS).isHierarchy) hA hbot hD)
    (fun B => forestDist σ.clusters σ.length (fun l => (s l : X)) B)
    (fun D => forestDist (σ.restrict S hS).clusters (σ.restrict S hS).length s D)
    (fun B hB hBS G => marg_forestDist_eq_empty hH σ.length (mem_childClusters.1 hB).1
      (fun l hl => hBS ⟨s l, mem_inter.2 ⟨hl, (s l).2⟩⟩) G)
    (fun B hB hBS => ?_) _ F
  funext G
  have hlen : (σ.restrict S hS).length (B.subtype (· ∈ S)) = marg_len σ S B := by
    show σ.restrictLength S _ = _
    rw [SpeciesTree.restrictLength, marg_filter_top hH hA hB hBS (hbot B hB), marg_len]
  rw [ih B hB hBS G, forestDist_eq_sum_entering]
  unfold populationKernel
  simp only [show _ ≠ univ from ne_top_of_lt (mem_childClusters.1 (marg_subtype_mem_childClusters hH hA hB hBS (hbot B hB))).2.1, hlen,
    show B ≠ univ from ne_top_of_lt (mem_childClusters.1 hB).2.1, ite_false]

/-- Pruning: the forest leaving a cluster `A` meeting `S` is the forest entering the trace of `A`
in the induced tree, evolved for the lengths of the clusters below `A` with the same trace. -/
theorem marg_prune (σ : SpeciesTree X) {S : Finset X} (hS : S.Nonempty) (s : L → S)
    {A : Finset X} (hA : A ∈ σ.clusters) (hAS : (A ∩ S).Nonempty) (G : Finset (Finset L)) :
    forestDist σ.clusters σ.length (fun l => (s l : X)) A G =
      ∑ F, enteringDist (σ.restrict S hS).clusters (σ.restrict S hS).length s
          (A.subtype (· ∈ S)) F * populationKernel (marg_len σ S) A F G := by
  have hH := σ.isHierarchy
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist_eq_sum_entering]
  by_cases hc : ∃ B₀ ∈ childClusters σ.clusters A, B₀.subtype (· ∈ S) = A.subtype (· ∈ S)
  · obtain ⟨B₀, hB₀, htr⟩ := hc
    obtain ⟨hB₀H, hB₀A, -⟩ := mem_childClusters.1 hB₀
    have hlen : marg_len σ S A = σ.length A + marg_len σ S B₀ := by
      rw [marg_len, marg_filter_chain hH hB₀ htr hAS hA,
        sum_insert fun h => not_subset_of_ssubset hB₀A (mem_filter.1 h).2.1, marg_len, htr]
    simp_rw [marg_enteringDist_chain hH σ.length (fun l => (s l).2) hB₀ htr,
      ih B₀ hB₀A hB₀H (subtype_nonempty_iff.1 (htr ▸ subtype_nonempty_iff.2 hAS)), sum_mul, htr]
    rw [sum_comm]
    refine sum_congr rfl fun F₀ _ => ?_
    simp_rw [mul_assoc, ← mul_sum]
    refine mul_eq_mul_left_iff.2 (or_iff_not_imp_right.2 fun h0 => ?_)
    unfold populationKernel
    simp [show B₀ ≠ univ from ne_top_of_lt hB₀A, ite_false]
    split_ifs
    · rw [kingmanTransition_mul_kingmanAbsorption
        (enteringDist_support (σ.restrict S hS).isHierarchy _ s h0).1]
    · rw [hlen, add_comm, kingmanTransition_add, Matrix.mul_apply]
  · push Not at hc
    refine sum_congr rfl fun F _ => ?_
    rw [marg_enteringDist_restrict σ hS s hA hc (fun B hB hBS => ih B (mem_childClusters.1 hB).2.1
      (mem_childClusters.1 hB).1 hBS) F]
    unfold populationKernel
    rw [marg_len, marg_filter_bot hH hA hc, sum_singleton]

/-- Pruning the species tree: if all lineages are sampled from taxa in `S`, the multispecies
coalescent on `σ` is the multispecies coalescent on the induced species tree `σ(S)`. -/
theorem SpeciesTree.rootedDist_restrict (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty)
    (s : L → S) (G : Finset (Finset L)) :
    (σ.restrict S hS).rootedDist s G = σ.rootedDist (fun l => (s l : X)) G := by
  unfold SpeciesTree.rootedDist
  rw [marg_prune σ hS s σ.univ_mem (by simpa using hS), forestDist_eq_sum_entering, subtype_univ]
  simp [populationKernel]

/-! ### Unrooting -/

/-- The restriction of an unrooted tree (given by the sides of its splits, as in `ADR11.unroot`)
to the lineages `L'`, along an embedding `e : L' ↪ L`: the splits whose two sides both meet the
range of `e`, restricted to `L'`. -/
def restrictUnrooted (e : L' ↪ L) (T : Finset (Finset L)) : Finset (Finset L') :=
  (T.filter fun A => (∃ l, e l ∈ A) ∧ ∃ l, e l ∉ A).image fun A => univ.filter fun l => e l ∈ A

theorem marg_tr_compl (e : L' ↪ L) (A : Finset L) :
    (univ.filter fun l => e l ∈ A)ᶜ = univ.filter fun l => e l ∈ Aᶜ := by aesop

theorem marg_tr_ne_univ (e : L' ↪ L) {A : Finset L} :
    (univ.filter fun l => e l ∈ A) ≠ univ ↔ ∃ l, e l ∉ A := by aesop

/-- Unrooting commutes with restricting to a subset of the lineages, for any family of clusters. -/
theorem marg_unroot_restrictForest (e : L' ↪ L) (G : Finset (Finset L)) :
    unroot (restrictForest e G) = restrictUnrooted e (unroot G) := by
  have key : ∀ D, (D ∈ restrictForest e G ∧ D ≠ univ) ↔
      ∃ A ∈ G, ((∃ l, e l ∈ A) ∧ ∃ l, e l ∉ A) ∧ (univ.filter fun l => e l ∈ A) = D := by
    simp only [marg_mem_restrictForest, ← marg_tr_ne_univ e]
    grind
  ext D
  rw [mem_unroot, key, key]
  simp only [restrictUnrooted, mem_image, mem_filter, mem_unroot]
  constructor
  · rintro (⟨A, hA, hp, rfl⟩ | ⟨A, hA, hp, hAD⟩) <;> have hu : A ≠ univ := by rintro rfl; simp at hp
    · grind
    · exact ⟨Aᶜ, ⟨Or.inr ⟨by rwa [compl_compl], by rwa [compl_compl]⟩, by simpa [and_comm] using hp⟩,
        by rw [← marg_tr_compl, hAD, compl_compl]⟩
  · rintro ⟨A, ⟨⟨hA, -⟩ | ⟨hA, -⟩, hp⟩, rfl⟩
    · grind
    · exact Or.inr ⟨Aᶜ, hA, by simpa [and_comm] using hp, marg_tr_compl e A ▸ rfl⟩

/-- Dropping lineages, for unrooted gene trees. -/
theorem SpeciesTree.unrootedDist_comp_embedding (σ : SpeciesTree X) (s : L → X) (e : L' ↪ L)
    (T' : Finset (Finset L')) :
    σ.unrootedDist (s ∘ e) T' =
      ∑ T, if restrictUnrooted e T = T' then σ.unrootedDist s T else 0 := by
  unfold SpeciesTree.unrootedDist
  simp_rw [σ.rootedDist_comp_embedding s e]
  rw [marg_sum_ite_comp (restrictForest e) unroot (σ.rootedDist s) T',
    marg_sum_ite_comp unroot (restrictUnrooted e) (σ.rootedDist s) T']
  simp_rw [marg_unroot_restrictForest]

end ADR11
