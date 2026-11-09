module

public import ADR11.Basic

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
  on the clusters `A ≠ univ` meeting `S`: the forest leaving `A` is the forest entering the trace
  `A ∩ S` in `σ(S)`, evolved for the sum of the lengths of the clusters `A' ⊆ A` with the same
  trace (a chain).
* `unroot_restrictForest`: unrooting commutes with restricting (for any family of clusters).
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {L : Type*} [Fintype L] [DecidableEq L] {L' : Type*} [Fintype L'] [DecidableEq L']

local notation "tr" e:max A:max => Finset.filter (fun l => e l ∈ A) univ
local notation "sub" S:max A:max => Finset.subtype (· ∈ S) A

def restrictForest (e : L' ↪ L) (F : Finset (Finset L)) : Finset (Finset L') :=
  (F.filter fun A => ∃ l, e l ∈ A).image fun A => tr e A

private theorem marg_mem_restrictForest (e : L' ↪ L) {F : Finset (Finset L)} {D : Finset L'} :
    D ∈ restrictForest e F ↔ ∃ A ∈ F, (∃ l, e l ∈ A) ∧ tr e A = D := by
  simp [restrictForest, and_assoc]

private theorem marg_tr_mem_restrictForest (e : L' ↪ L) {F : Finset (Finset L)} {A : Finset L}
    (hA : A ∈ F) (hmeet : ∃ l, e l ∈ A) : tr e A ∈ restrictForest e F :=
  (marg_mem_restrictForest e).2 ⟨A, hA, hmeet, rfl⟩

private theorem marg_tr_mono (e : L' ↪ L) {A B : Finset L} (h : A ⊆ B) : tr e A ⊆ tr e B :=
  fun l hl => mem_filter.2 ⟨mem_univ l, h (mem_filter.1 hl).2⟩

private theorem marg_tr_eq_empty (e : L' ↪ L) {A : Finset L} (h : ¬ ∃ l, e l ∈ A) :
    tr e A = ∅ := by
  ext l; simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
  exact fun hl => h ⟨l, hl⟩

theorem IsForest.restrictForest {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L) :
    IsForest (restrictForest e F) := by
  refine ⟨fun D hD => ?_, fun D hD D' hD' => ?_⟩
  · obtain ⟨A, -, ⟨l, hl⟩, rfl⟩ := (marg_mem_restrictForest e).1 hD
    exact ⟨l, mem_filter.2 ⟨mem_univ l, hl⟩⟩
  · obtain ⟨A, hA, -, rfl⟩ := (marg_mem_restrictForest e).1 hD
    obtain ⟨B, hB, -, rfl⟩ := (marg_mem_restrictForest e).1 hD'
    rcases hF.2 A hA B hB with h | h | h
    · exact Or.inl (marg_tr_mono e h)
    · exact Or.inr (Or.inl (marg_tr_mono e h))
    · exact Or.inr (Or.inr (disjoint_left.2 fun _ hlA hlB =>
        disjoint_left.1 h (mem_filter.1 hlA).2 (mem_filter.1 hlB).2))

private theorem marg_tr_inj {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L)
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) (hmeet : ∃ l, e l ∈ A)
    (h : tr e A = tr e B) : A = B := by
  obtain ⟨l, hl⟩ := hmeet
  have hlB : l ∈ tr e B := h ▸ mem_filter.2 ⟨mem_univ l, hl⟩
  exact hF.eq_of_mem_roots_of_mem hA hB hl (mem_filter.1 hlB).2

private theorem marg_mem_roots_restrictForest {F : Finset (Finset L)} (hF : IsForest F)
    (e : L' ↪ L) {D : Finset L'} :
    D ∈ roots (restrictForest e F) ↔ ∃ A ∈ roots F, (∃ l, e l ∈ A) ∧ tr e A = D := by
  constructor
  · intro hD
    obtain ⟨hDF, hmax⟩ := mem_roots.1 hD
    obtain ⟨A, hA, ⟨l, hl⟩, rfl⟩ := (marg_mem_restrictForest e).1 hDF
    obtain ⟨R, hR, hAR⟩ := exists_mem_roots_subset hA
    exact ⟨R, hR, ⟨l, hAR hl⟩,
      hmax _ (marg_tr_mem_restrictForest e (roots_subset F hR) ⟨l, hAR hl⟩) (marg_tr_mono e hAR)⟩
  · rintro ⟨A, hA, hmeet, rfl⟩
    refine mem_roots.2 ⟨marg_tr_mem_restrictForest e (roots_subset F hA) hmeet, fun D hD hAD => ?_⟩
    obtain ⟨B, hB, -, rfl⟩ := (marg_mem_restrictForest e).1 hD
    obtain ⟨R, hR, hBR⟩ := exists_mem_roots_subset hB
    obtain ⟨l, hl⟩ := hmeet
    have hlB : e l ∈ B := (mem_filter.1 (hAD (mem_filter.2 ⟨mem_univ l, hl⟩))).2
    have hAR : A = R := hF.eq_of_mem_roots_of_mem hA hR hl (hBR hlB)
    exact subset_antisymm (marg_tr_mono e (hAR ▸ hBR)) hAD

private theorem marg_restrictForest_merge {F : Finset (Finset L)} (e : L' ↪ L)
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) :
    restrictForest e (insert (A ∪ B) F) =
      if (∃ l, e l ∈ A) ∧ (∃ l, e l ∈ B) then insert (tr e A ∪ tr e B) (restrictForest e F)
      else restrictForest e F := by
  have hins : restrictForest e (insert (A ∪ B) F) =
      if ∃ l, e l ∈ A ∪ B then insert (tr e A ∪ tr e B) (restrictForest e F)
      else restrictForest e F := by
    unfold restrictForest; rw [filter_insert]; split_ifs <;> simp [image_insert, filter_or]
  rw [hins]
  by_cases hAm : ∃ l, e l ∈ A <;> by_cases hBm : ∃ l, e l ∈ B <;>
    simp only [mem_union, exists_or, hAm, hBm, and_self, and_false, false_and, or_self, or_true,
      true_or, ↓reduceIte]
  · rw [marg_tr_eq_empty e hBm, union_empty,
      insert_eq_of_mem (marg_tr_mem_restrictForest e (roots_subset F hA) hAm)]
  · rw [marg_tr_eq_empty e hAm, empty_union,
      insert_eq_of_mem (marg_tr_mem_restrictForest e (roots_subset F hB) hBm)]

private theorem marg_merge_roots {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L)
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) (hAB : A ≠ B)
    (hAm : ∃ l, e l ∈ A) (hBm : ∃ l, e l ∈ B) :
    tr e A ∈ roots (restrictForest e F) ∧ tr e B ∈ roots (restrictForest e F) ∧
      tr e A ≠ tr e B ∧ insert (tr e A ∪ tr e B) (restrictForest e F) ∈ merges (restrictForest e F) := by
  have hrA := (marg_mem_roots_restrictForest hF e).2 ⟨A, hA, hAm, rfl⟩
  have hrB := (marg_mem_roots_restrictForest hF e).2 ⟨B, hB, hBm, rfl⟩
  have hne : tr e A ≠ tr e B := fun h => hAB (marg_tr_inj hF e hA hB hAm h)
  exact ⟨hrA, hrB, hne, mem_merges.2 ⟨_, hrA, _, hrB, hne, rfl⟩⟩

private theorem marg_mem_merges_ne {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L)
    {H : Finset (Finset L)} :
    (H ∈ merges F ∧ restrictForest e H ≠ restrictForest e F) ↔
      ∃ A ∈ roots F, ∃ B ∈ roots F, A ≠ B ∧ (∃ l, e l ∈ A) ∧ (∃ l, e l ∈ B) ∧
        H = insert (A ∪ B) F := by
  constructor
  · rintro ⟨hH, hne⟩
    obtain ⟨A, hA, B, hB, hAB, rfl⟩ := mem_merges.1 hH
    rw [marg_restrictForest_merge e hA hB] at hne
    by_cases h : (∃ l, e l ∈ A) ∧ (∃ l, e l ∈ B)
    · exact ⟨A, hA, B, hB, hAB, h.1, h.2, rfl⟩
    · exact absurd (ite_eq_right h) hne
  · rintro ⟨A, hA, B, hB, hAB, hAm, hBm, rfl⟩
    rw [marg_restrictForest_merge e hA hB, ite_eq_left ⟨hAm, hBm⟩]
    exact ⟨mem_merges.2 ⟨A, hA, B, hB, hAB, rfl⟩,
      ((hF.restrictForest e).of_mem_merges (marg_merge_roots hF e hA hB hAB hAm hBm).2.2.2).2.2.2.1⟩

private theorem marg_sum_merges {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L)
    (u : Finset (Finset L') → ℝ) :
    -((#(roots F)).choose 2 : ℝ) * u (restrictForest e F) +
        ∑ H ∈ merges F, u (restrictForest e H) =
      -((#(roots (restrictForest e F))).choose 2 : ℝ) * u (restrictForest e F) +
        ∑ H' ∈ merges (restrictForest e F), u H' := by
  set rF := restrictForest e F with hrF
  have hrFf : IsForest rF := hF.restrictForest e
  set M₂ := (merges F).filter fun H => restrictForest e H ≠ rF with hM₂
  have himage : M₂.image (restrictForest e) = merges rF := by
    ext H'; rw [mem_image]
    constructor
    · rintro ⟨H, hH, rfl⟩
      obtain ⟨A, hA, B, hB, hAB, hAm, hBm, rfl⟩ := (marg_mem_merges_ne hF e).1 (mem_filter.1 hH)
      rw [marg_restrictForest_merge e hA hB, ite_eq_left ⟨hAm, hBm⟩]
      exact (marg_merge_roots hF e hA hB hAB hAm hBm).2.2.2
    · intro hH'
      obtain ⟨A', hA', B', hB', hAB', rfl⟩ := mem_merges.1 hH'
      obtain ⟨A, hA, hAm, rfl⟩ := (marg_mem_roots_restrictForest hF e).1 hA'
      obtain ⟨B, hB, hBm, rfl⟩ := (marg_mem_roots_restrictForest hF e).1 hB'
      refine ⟨insert (A ∪ B) F, mem_filter.2 ((marg_mem_merges_ne hF e).2
        ⟨A, hA, B, hB, fun e => hAB' (e ▸ rfl), hAm, hBm, rfl⟩), ?_⟩
      rw [marg_restrictForest_merge e hA hB, ite_eq_left ⟨hAm, hBm⟩]
  have hinj : Set.InjOn (restrictForest e) (M₂ : Set (Finset (Finset L))) := by
    intro H₁ hH₁ H₂ hH₂ h12
    obtain ⟨A₁, hA₁, B₁, hB₁, hAB₁, hA₁m, hB₁m, rfl⟩ :=
      (marg_mem_merges_ne hF e).1 (mem_filter.1 (mem_coe.1 hH₁))
    obtain ⟨A₂, hA₂, B₂, hB₂, hAB₂, hA₂m, hB₂m, rfl⟩ :=
      (marg_mem_merges_ne hF e).1 (mem_filter.1 (mem_coe.1 hH₂))
    rw [marg_restrictForest_merge e hA₁ hB₁, ite_eq_left ⟨hA₁m, hB₁m⟩,
      marg_restrictForest_merge e hA₂ hB₂, ite_eq_left ⟨hA₂m, hB₂m⟩] at h12
    obtain ⟨hrA₁, hrB₁, hne₁, -⟩ := marg_merge_roots hF e hA₁ hB₁ hAB₁ hA₁m hB₁m
    obtain ⟨hrA₂, hrB₂, hne₂, -⟩ := marg_merge_roots hF e hA₂ hB₂ hAB₂ hA₂m hB₂m
    rcases Sym2.eq_iff.1 (hrFf.merge_inj hrA₁ hrB₁ hne₁ hrA₂ hrB₂ hne₂ h12) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [marg_tr_inj hF e hA₁ hA₂ hA₁m h1, marg_tr_inj hF e hB₁ hB₂ hB₁m h2]
    · rw [marg_tr_inj hF e hA₁ hB₂ hA₁m h1, marg_tr_inj hF e hB₁ hA₂ hB₁m h2, union_comm]
  have hcard₂ : #M₂ = (#(roots rF)).choose 2 := by
    rw [← card_image_of_injOn hinj, himage, hrFf.card_merges]
  have hcard : #((merges F).filter fun H => restrictForest e H = rF) + #M₂ =
      (#(roots F)).choose 2 := by
    rw [hM₂, card_filter_add_card_filter_not, hF.card_merges]
  have hsum : ∑ H ∈ merges F, u (restrictForest e H) =
      #((merges F).filter fun H => restrictForest e H = rF) * u rF + ∑ H' ∈ merges rF, u H' := by
    rw [← sum_filter_add_sum_filter_not (merges F) (fun H => restrictForest e H = rF),
      sum_congr rfl fun H hH => by rw [(mem_filter.1 hH).2], sum_const, nsmul_eq_mul,
      ← himage, sum_image hinj]
  have hcard' : ((#((merges F).filter fun H => restrictForest e H = rF) : ℕ) : ℝ) =
      ((#(roots F)).choose 2 : ℝ) - ((#(roots rF)).choose 2 : ℝ) := by
    rw [← hcard, ← hcard₂]; push_cast; ring
  rw [hsum, hcard']; ring

private theorem marg_sum_kingmanGenerator_pow (e : L' ↪ L) (n : ℕ) {F : Finset (Finset L)}
    (hF : IsForest F) (w : Finset (Finset L') → ℝ) :
    ∑ G, (kingmanGenerator ^ n) F G * w (restrictForest e G) =
      ∑ G', (kingmanGenerator ^ n) (restrictForest e F) G' * w G' := by
  induction n generalizing F w with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ,
      ite_true]
  | succ n ih =>
    set u : Finset (Finset L') → ℝ := fun H' => ∑ G', (kingmanGenerator ^ n) H' G' * w G'
      with hu
    have hstep (H : Finset (Finset L)) : kingmanGenerator F H *
        ∑ G, (kingmanGenerator ^ n) H G * w (restrictForest e G) =
          kingmanGenerator F H * u (restrictForest e H) := by
      by_cases hQ : kingmanGenerator F H = 0
      · rw [hQ, zero_mul, zero_mul]
      · have hH : IsForest H := by
          rw [kingmanGenerator_apply_of_isForest] at hQ
          split_ifs at hQ with h1 h2
          · exact h1 ▸ hF
          · exact (hF.of_mem_merges h2).1
          · exact absurd rfl hQ
        rw [ih hH w]
    simp_rw [pow_succ', Matrix.mul_apply, sum_mul, mul_assoc]
    rw [sum_comm, sum_congr rfl fun H _ => by rw [← mul_sum, hstep],
      hF.sum_kingmanGenerator_mul (fun G => u (restrictForest e G)),
      marg_sum_merges hF e u, ← (hF.restrictForest e).sum_kingmanGenerator_mul u,
      sum_comm]
    simp_rw [hu, mul_sum]

theorem kingmanTransition_lump {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L) (t : ℝ)
    (G' : Finset (Finset L')) :
    ∑ G, (if restrictForest e G = G' then kingmanTransition t F G else 0) =
      kingmanTransition t (restrictForest e F) G' := by
  set w : Finset (Finset L') → ℝ := fun G'' => if G'' = G' then 1 else 0
  have h1 : HasSum (fun n : ℕ => ∑ G, ((n.factorial : ℝ))⁻¹ *
      ((t • kingmanGenerator (L := L)) ^ n) F G * w (restrictForest e G))
      (∑ G, kingmanTransition t F G * w (restrictForest e G)) :=
    hasSum_sum fun G _ => (fact_hasSum_exp_apply _ F G).mul_right _
  have h2 : HasSum (fun n : ℕ => ∑ G'', ((n.factorial : ℝ))⁻¹ *
      ((t • kingmanGenerator (L := L')) ^ n) (restrictForest e F) G'' * w G'')
      (∑ G'', kingmanTransition t (restrictForest e F) G'' * w G'') :=
    hasSum_sum fun G'' _ => (fact_hasSum_exp_apply _ _ G'').mul_right _
  have h := h1.unique (by
    convert h2 using 1; funext n
    simp_rw [smul_pow, Matrix.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum]
    rw [marg_sum_kingmanGenerator_pow e n hF w])
  simpa only [w, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true] using h

theorem kingmanAbsorption_lump {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L)
    (G' : Finset (Finset L')) :
    ∑ G, (if restrictForest e G = G' then kingmanAbsorption F G else 0) =
      kingmanAbsorption (restrictForest e F) G' := by
  have h1 : Filter.Tendsto
      (fun t => ∑ G, (if restrictForest e G = G' then kingmanTransition t F G else 0))
      Filter.atTop
      (nhds (∑ G, (if restrictForest e G = G' then kingmanAbsorption F G else 0))) :=
    tendsto_finsetSum _ fun G _ => by
      split_ifs; exacts [tendsto_kingmanTransition hF G, tendsto_const_nhds]
  simp_rw [kingmanTransition_lump hF e] at h1
  exact tendsto_nhds_unique h1 (tendsto_kingmanTransition (hF.restrictForest e) G')

private theorem marg_restrictForest_union (e : L' ↪ L) (F₁ F₂ : Finset (Finset L)) :
    restrictForest e (F₁ ∪ F₂) = restrictForest e F₁ ∪ restrictForest e F₂ := by
  unfold restrictForest; rw [filter_union, image_union]

private theorem marg_restrictForest_sampledForest (e : L' ↪ L) (s : L → X) (A : Finset X) :
    restrictForest e (sampledForest s A) = sampledForest (s ∘ e) A := by
  ext D
  rw [marg_mem_restrictForest, mem_sampledForest]
  constructor
  · rintro ⟨_, hC, ⟨l', hl'⟩, rfl⟩
    obtain ⟨l, hl, rfl⟩ := mem_sampledForest.1 hC
    rw [mem_singleton] at hl'; subst hl'
    refine ⟨l', hl, ?_⟩; ext m; simp [e.injective.eq_iff, eq_comm]
  · rintro ⟨l', hl', rfl⟩
    refine ⟨{e l'}, mem_sampledForest.2 ⟨e l', hl', rfl⟩, ⟨l', mem_singleton_self _⟩, ?_⟩
    ext m; simp [e.injective.eq_iff]

private theorem marg_sum_ite_comp {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [DecidableEq γ] (f : α → β) (g : β → γ) (p : α → ℝ) (c : γ) :
    ∑ b, (if g b = c then ∑ a, (if f a = b then p a else 0) else 0) =
      ∑ a, if g (f a) = c then p a else 0 := by
  have h (b) : (if g b = c then ∑ a, (if f a = b then p a else 0) else 0) =
      ∑ a, if f a = b then (if g b = c then p a else 0) else 0 := by split_ifs <;> simp
  simp_rw [h]; rw [sum_comm]
  exact sum_congr rfl fun a _ => by rw [sum_ite_eq]; simp

theorem forestDist_comp_embedding {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) (s : L → X) (e : L' ↪ L) {A : Finset X} (hA : A ∈ H)
    (G' : Finset (Finset L')) :
    forestDist H len (s ∘ e) A G' =
      ∑ G, if restrictForest e G = G' then forestDist H len s A G else 0 := by
  induction A using Finset.strongInduction generalizing G' with
  | H A ih =>
  have hent (F') : enteringDist H len (s ∘ e) A F' =
      ∑ F, if restrictForest e F = F' then enteringDist H len s A F else 0 := by
    unfold enteringDist
    rw [marg_sum_ite_comp (fun f : childClusters H A → Finset (Finset L) =>
        univ.sup f ∪ sampledForest s A) (restrictForest e)]
    have hP (f' : childClusters H A → Finset (Finset L')) :
        ∏ B : childClusters H A, forestDist H len (s ∘ e) B (f' B) =
          ∑ f : childClusters H A → Finset (Finset L),
            if (fun B => restrictForest e (f B)) = f' then
              ∏ B : childClusters H A, forestDist H len s B (f B) else 0 := by
      rw [prod_congr rfl fun (B : childClusters H A) _ =>
        ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1 (f' B), Fintype.prod_sum]
      exact sum_congr rfl fun f _ => by rw [prod_ite_zero]; simp [funext_iff]
    simp_rw [hP]
    rw [marg_sum_ite_comp (fun f : childClusters H A → Finset (Finset L) =>
        fun B => restrictForest e (f B)) (fun f' => univ.sup f' ∪ sampledForest (s ∘ e) A)]
    refine sum_congr rfl fun f _ => ?_
    rw [marg_restrictForest_union,
      Finset.apply_sup_eq_sup_comp (restrictForest e) (marg_restrictForest_union e) (by simp [restrictForest]),
      marg_restrictForest_sampledForest]
    rfl
  have hK (F) : enteringDist H len s A F * ∑ G, (if restrictForest e G = G' then
      populationKernel len A F G else 0) =
        enteringDist H len s A F * populationKernel len A (restrictForest e F) G' := by
    by_cases h0 : enteringDist H len s A F = 0
    · rw [h0, zero_mul, zero_mul]
    · congr 1
      have hF := enteringDist_support hH len s h0
      unfold populationKernel
      split_ifs; exacts [kingmanAbsorption_lump hF e G', kingmanTransition_lump hF e _ G']
  rw [forestDist_eq_sum_entering]
  simp_rw [hent, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  simp_rw [sum_ite_eq, mem_univ, ite_true, ← hK, mul_sum, mul_ite, mul_zero]
  rw [sum_comm]
  refine sum_congr rfl fun G _ => ?_
  rw [forestDist_eq_sum_entering]; split_ifs <;> simp

private theorem marg_sum_pi_reindex {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι']
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
  have hji (i : T) (hP : P i) : (⟨j (τ i) (hmaps i i.2 hP), hjT _ _⟩ : T) = i :=
    Subtype.ext (hinj _ (hjT _ _) i i.2 (hjP _ _) hP (hjτ _ _))
  have hij (i' : T') : (⟨τ (j i'.1 i'.2), hmaps _ (hjT _ _) (hjP _ _)⟩ : T') = i' :=
    Subtype.ext (hjτ _ _)
  rw [← sum_subset (filter_subset (fun f : T → Finset (Finset L) => ∀ i : T, ¬ P i → f i = ∅) univ)
    fun f _ hf => by
      simp only [mem_filter, mem_univ, true_and, not_forall] at hf
      obtain ⟨i, hPi, hfi⟩ := hf
      rw [prod_eq_zero (mem_univ i) (by rw [h0 i i.2 hPi, ite_eq_right hfi]), ite_self]]
  refine sum_nbij' (fun f i' => f ⟨j i'.1 i'.2, hjT _ _⟩)
    (fun g i => if h : P i then g ⟨τ i, hmaps i i.2 h⟩ else ∅)
    (fun _ _ => mem_univ _)
    (fun g _ => mem_filter.2 ⟨mem_univ _, fun i hi => dite_eq_right hi⟩)
    (fun f hf => funext fun i => by by_cases hi : P i <;> simp [hi, hji i, (mem_filter.1 hf).2 i])
    (fun g _ => funext fun i' => by dsimp only; rw [dite_eq_left (hjP _ _), hij i'])
    fun f hf => ?_
  have hf' := (mem_filter.1 hf).2
  have hsup : univ.sup f = univ.sup fun i' : T' => f ⟨j i'.1 i'.2, hjT _ _⟩ :=
    le_antisymm (Finset.sup_le fun i _ => if hi : P i then
      hji i hi ▸ le_sup (f := fun i' : T' => f ⟨j i'.1 i'.2, hjT _ _⟩) (mem_univ ⟨τ i, hmaps i i.2 hi⟩)
      else by rw [hf' i hi]; exact bot_le) (Finset.sup_le fun _ _ => le_sup (f := f) (mem_univ _))
  have hprod : ∏ i : T, φ i (f i) = ∏ i' : T', ψ i' (f ⟨j i'.1 i'.2, hjT _ _⟩) := by
    rw [← prod_filter_of_ne (p := fun i : T => P i) fun i _ hne =>
      by_contra fun hi => hne (by rw [h0 i i.2 hi, hf' i hi, ite_eq_left rfl])]
    exact prod_bij' (fun i hi => ⟨τ i, hmaps i i.2 (mem_filter.1 hi).2⟩)
      (fun i' _ => ⟨j i'.1 i'.2, hjT _ _⟩) (fun _ _ => mem_univ _)
      (fun i' _ => mem_filter.2 ⟨mem_univ _, hjP _ _⟩)
      (fun i hi => hji i (mem_filter.1 hi).2) (fun i' _ => hij i')
      (fun i hi => by dsimp only; rw [h1 i i.2 (mem_filter.1 hi).2, hji i (mem_filter.1 hi).2])
  dsimp only; rw [hsup, hprod]

private theorem marg_subtype_mem_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {S A B : Finset X} (hA : A ∈ H) (hB : B ∈ childClusters H A) (hBS : (B ∩ S).Nonempty)
    (hne : sub S B ≠ sub S A) :
    sub S B ∈ childClusters (restrictClusters S H) (sub S A) := by
  obtain ⟨hBH, hBA, hBmax⟩ := mem_childClusters.1 hB
  refine mem_childClusters.2 ⟨mem_restrictClusters.2 ⟨B, hBH, hBS, rfl⟩,
    (subtype_mono hBA.subset).ssubset_of_ne hne, fun E' hE' hBE' hE'A => ?_⟩
  obtain ⟨E, hE, -, rfl⟩ := mem_restrictClusters.1 hE'
  obtain ⟨x, hx⟩ := subtype_nonempty_iff.2 hBS
  have hxB : (x : X) ∈ B := mem_subtype.1 hx
  have hxE : (x : X) ∈ E := mem_subtype.1 (hBE'.subset hx)
  rcases hH.subset_or_subset_of_mem hE hA hxE (hBA.subset hxB) with hEA | hAE
  · rcases hH.subset_or_subset_of_mem hE hBH hxE hxB with hEB | hBE
    · exact not_subset_of_ssubset hBE' (subtype_mono hEB)
    · exact hBmax E hE (hBE.ssubset_of_ne fun e => lt_irrefl _ (e ▸ hBE'))
        (hEA.ssubset_of_ne fun e => lt_irrefl _ (e ▸ hE'A))
  · exact not_subset_of_ssubset hE'A (subtype_mono hAE)

private theorem marg_exists_child {H : Finset (Finset X)} (hH : IsHierarchy H) {S A : Finset X}
    (hH' : IsHierarchy (restrictClusters S H)) (hA : A ∈ H)
    (hbot : ∀ B ∈ childClusters H A, sub S B ≠ sub S A)
    {D : Finset S} (hD : D ∈ childClusters (restrictClusters S H) (sub S A)) :
    ∃ B ∈ childClusters H A, (B ∩ S).Nonempty ∧ sub S B = D := by
  obtain ⟨hDH, hDA, -⟩ := mem_childClusters.1 hD
  obtain ⟨x, hx⟩ := hH'.2.2.1 D hDH
  obtain ⟨y, hyA, hyD⟩ := exists_of_ssubset hDA
  have hxA : (x : X) ∈ A := mem_subtype.1 (hDA.subset hx)
  have hA2 : 2 ≤ #A := one_lt_card.2 ⟨x, hxA, y, mem_subtype.1 hyA, fun h => hyD (Subtype.ext h ▸ hx)⟩
  obtain ⟨B, hB, hxB⟩ := hH.exists_mem_childClusters hA2 hxA
  have hBS : (B ∩ S).Nonempty := ⟨x, mem_inter.2 ⟨hxB, x.2⟩⟩
  exact ⟨B, hB, hBS, by_contra fun hne => Finset.disjoint_left.1
    (hH'.disjoint_of_mem_childClusters (marg_subtype_mem_childClusters hH hA hB hBS (hbot B hB)) hD hne)
    (mem_subtype.2 hxB) hx⟩

set_option quotPrecheck false in
local notation "chain" H:max S:max A:max =>
  Finset.filter (fun A' => A' ⊆ A ∧ sub S A' = sub S A) H

private theorem marg_filter_top {H : Finset (Finset X)} (hH : IsHierarchy H) {S A B : Finset X}
    (hA : A ∈ H) (hB : B ∈ childClusters H A) (hBS : (B ∩ S).Nonempty)
    (hne : sub S B ≠ sub S A) :
    H.filter (fun A' => A' ≠ univ ∧ sub S A' = sub S B) = chain H S B := by
  obtain ⟨hBH, hBA, hBmax⟩ := mem_childClusters.1 hB
  ext A'; simp only [mem_filter]
  refine ⟨fun ⟨hA'H, _, htr⟩ => ⟨hA'H, ?_, htr⟩, fun ⟨hA'H, hA'B, htr⟩ =>
    ⟨hA'H, fun h => not_subset_of_ssubset hBA ((h ▸ hA'B).trans' (subset_univ A)), htr⟩⟩
  obtain ⟨x, hx⟩ := subtype_nonempty_iff.2 hBS
  have hxB : (x : X) ∈ B := mem_subtype.1 hx
  have hxA' : (x : X) ∈ A' := mem_subtype.1 (htr.symm ▸ hx)
  rcases hH.subset_or_subset_of_mem hA'H hBH hxA' hxB with h | hBA'
  · exact h
  · refine hBA'.eq_or_ssubset.elim (·.symm.subset) fun hBA' => False.elim ?_
    rcases hH.subset_or_subset_of_mem hA'H hA hxA' (hBA.subset hxB) with hA'A | hAA'
    · exact hA'A.eq_or_ssubset.elim (fun e => hne (e ▸ htr.symm)) (hBmax A' hA'H hBA')
    · exact hne (subset_antisymm (subtype_mono hBA.subset) (htr ▸ subtype_mono hAA'))

private theorem marg_filter_chain {H : Finset (Finset X)} (hH : IsHierarchy H) {S A B₀ : Finset X}
    (hB₀ : B₀ ∈ childClusters H A) (htr : sub S B₀ = sub S A)
    (hAS : (A ∩ S).Nonempty) (hA : A ∈ H) :
    chain H S A = insert A (chain H S B₀) := by
  obtain ⟨hB₀H, hB₀A, -⟩ := mem_childClusters.1 hB₀
  ext A'; simp only [mem_insert, mem_filter]
  refine ⟨fun ⟨hA'H, hA'A, htr'⟩ => hA'A.eq_or_ssubset.imp_right fun hA'A => ⟨hA'H, ?_, htr'.trans htr.symm⟩,
    by rintro (rfl | ⟨hA'H, hA'B₀, htr'⟩)
       · exact ⟨hA, subset_rfl, rfl⟩
       · exact ⟨hA'H, hA'B₀.trans hB₀A.subset, htr'.trans htr⟩⟩
  obtain ⟨B, hB, hA'B⟩ := hH.exists_mem_childClusters_superset hA'H hA'A
  obtain ⟨x, hx⟩ := subtype_nonempty_iff.2 hAS
  have hBB₀ : B = B₀ := by_contra fun hne =>
    Finset.disjoint_left.1 (hH.disjoint_of_mem_childClusters hB hB₀ hne)
      (hA'B (mem_subtype.1 (htr'.symm ▸ hx))) (mem_subtype.1 (htr.symm ▸ hx))
  exact hBB₀ ▸ hA'B

private theorem marg_filter_bot {H : Finset (Finset X)} (hH : IsHierarchy H) {S A : Finset X}
    (hA : A ∈ H) (hbot : ∀ B ∈ childClusters H A, sub S B ≠ sub S A) :
    chain H S A = {A} := by
  ext A'; simp only [mem_filter, mem_singleton]
  refine ⟨fun ⟨hA'H, hA'A, htr'⟩ => by_contra fun hne => ?_, by rintro rfl; exact ⟨hA, subset_rfl, rfl⟩⟩
  obtain ⟨B, hB, hA'B⟩ := hH.exists_mem_childClusters_superset hA'H (hA'A.ssubset_of_ne hne)
  exact hbot B hB (subset_antisymm (subtype_mono (mem_childClusters.1 hB).2.1.subset)
    (htr' ▸ subtype_mono hA'B))

private theorem marg_forestDist_eq_empty {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) {s : L → X} {B : Finset X} (hB : B ∈ H) (hs : ∀ l, s l ∉ B)
    (G : Finset (Finset L)) : forestDist H len s B G = if G = ∅ then 1 else 0 := by
  have hz (G : Finset (Finset L)) (hG : G ≠ ∅) : forestDist H len s B G = 0 := by
    by_contra h
    obtain ⟨hGf, -, hlin⟩ := forestDist_support hH len s hB h
    obtain ⟨C, hC⟩ := nonempty_iff_ne_empty.2 hG
    obtain ⟨l, hl⟩ := hGf.1 C hC
    have hl' := subset_lineages hC hl
    rw [hlin, mem_filter] at hl'
    exact hs l hl'.2
  split_ifs with hG
  · subst hG
    have hsum := forestDist_sum hH len s hB
    rwa [← sum_erase_add _ _ (mem_univ ∅), sum_eq_zero fun G hG => hz G (ne_of_mem_erase hG),
      zero_add] at hsum
  · exact hz G hG

private theorem marg_enteringDist_chain {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) {S : Finset X} {s : L → X} (hs : ∀ l, s l ∈ S) {A B₀ : Finset X}
    (hB₀ : B₀ ∈ childClusters H A) (htr : sub S B₀ = sub S A)
    (F : Finset (Finset L)) : enteringDist H len s A F = forestDist H len s B₀ F := by
  have hB₀A := (mem_childClusters.1 hB₀).2.1
  have hother : ∀ B ∈ childClusters H A, B ≠ B₀ → ∀ l, s l ∉ B := fun B hB hne l hl => by
    have h1 : (⟨s l, hs l⟩ : S) ∈ sub S A :=
      mem_subtype.2 ((mem_childClusters.1 hB).2.1.subset hl)
    rw [← htr, mem_subtype] at h1
    exact Finset.disjoint_left.1 (hH.disjoint_of_mem_childClusters hB hB₀ hne) hl h1
  have hSF : sampledForest s A = sampledForest s B₀ := by
    unfold sampledForest; congr 1; ext l
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => mem_subtype.1 (htr ▸ mem_subtype.2 h : (⟨s l, hs l⟩ : S) ∈ sub S B₀),
      fun h => hB₀A.subset h⟩
  unfold enteringDist
  rw [marg_sum_pi_reindex (T' := ({B₀} : Finset (Finset X))) (fun B => B = B₀) id
    (fun B _ h => h ▸ mem_singleton_self _) (fun B _ B' _ h h' _ => h.trans h'.symm)
    (fun i' hi' => ⟨B₀, hB₀, rfl, (mem_singleton.1 hi').symm⟩)
    (fun B => forestDist H len s B) (fun B => forestDist H len s B)
    (fun B hB hne F => marg_forestDist_eq_empty hH len (mem_childClusters.1 hB).1
      (hother B hB hne) F) (fun _ _ _ => rfl)]
  have hu : (univ : Finset ({B₀} : Finset (Finset X))) = {⟨B₀, mem_singleton_self _⟩} := by
    ext i; simp [Subtype.ext_iff, mem_singleton.1 i.2]
  have hterm (g : ({B₀} : Finset (Finset X)) → Finset (Finset L)) :
      (if univ.sup g ∪ sampledForest s A = F then
        ∏ i : ({B₀} : Finset (Finset X)), forestDist H len s i (g i) else 0) =
      if g = fun _ => F then forestDist H len s B₀ (g ⟨B₀, mem_singleton_self _⟩) else 0 := by
    rw [hu, sup_singleton, prod_singleton, hSF]; dsimp only [id]
    by_cases h0 : forestDist H len s B₀ (g ⟨B₀, mem_singleton_self _⟩) = 0
    · simp [h0]
    · rw [union_eq_left.2 (forestDist_support hH len s (mem_childClusters.1 hB₀).1 h0).2.1]
      congr 1; exact propext ⟨fun h => funext fun i => by
        rw [show i = ⟨B₀, mem_singleton_self _⟩ from Subtype.ext (mem_singleton.1 i.2), h],
        fun h => congrFun h _⟩
  simp_rw [hterm]; simp

private abbrev PruneEq (σ : SpeciesTree X) {S : Finset X} (hS : S.Nonempty) (s : L → S)
    (B : Finset X) : Prop :=
  ∀ G, forestDist σ.clusters σ.length (fun l => (s l : X)) B G =
    ∑ F, enteringDist (σ.restrict S hS).clusters (σ.restrict S hS).length s (sub S B) F *
      kingmanTransition (∑ A' ∈ chain σ.clusters S B, σ.length A') F G

private theorem marg_enteringDist_restrict (σ : SpeciesTree X) {S : Finset X} (hS : S.Nonempty)
    (s : L → S) {A : Finset X} (hA : A ∈ σ.clusters)
    (hbot : ∀ B ∈ childClusters σ.clusters A, sub S B ≠ sub S A)
    (ih : ∀ B ∈ childClusters σ.clusters A, (B ∩ S).Nonempty → PruneEq σ hS s B)
    (F : Finset (Finset L)) :
    enteringDist σ.clusters σ.length (fun l => (s l : X)) A F =
      enteringDist (σ.restrict S hS).clusters (σ.restrict S hS).length s (sub S A) F := by
  have hH := σ.isHierarchy
  have hH' : IsHierarchy (restrictClusters S σ.clusters) := (σ.restrict S hS).isHierarchy
  have hSF : sampledForest (fun l => (s l : X)) A = sampledForest s (sub S A) := by
    unfold sampledForest; congr 1; ext l; simp [mem_subtype]
  unfold enteringDist
  rw [hSF]
  refine marg_sum_pi_reindex (fun B => (B ∩ S).Nonempty) (fun B => sub S B)
    (fun B hB hBS => marg_subtype_mem_childClusters hH hA hB hBS (hbot B hB))
    (fun B₁ hB₁ B₂ hB₂ hB₁S _ h => by_contra fun hne =>
      let ⟨x, hx⟩ := subtype_nonempty_iff.2 hB₁S
      Finset.disjoint_left.1 (hH.disjoint_of_mem_childClusters hB₁ hB₂ hne)
        (mem_subtype.1 hx) (mem_subtype.1 (h ▸ hx)))
    (fun D hD => marg_exists_child hH hH' hA hbot hD)
    (fun B => forestDist σ.clusters σ.length (fun l => (s l : X)) B)
    (fun D => forestDist (σ.restrict S hS).clusters (σ.restrict S hS).length s D)
    (fun B hB hBS G => marg_forestDist_eq_empty hH σ.length (mem_childClusters.1 hB).1
      (fun l hl => hBS ⟨s l, mem_inter.2 ⟨hl, (s l).2⟩⟩) G)
    (fun B hB hBS => ?_) _ F
  funext G
  have hBc := marg_subtype_mem_childClusters hH hA hB hBS (hbot B hB)
  have hBu : sub S B ≠ univ :=
    fun h => not_subset_of_ssubset (h ▸ (mem_childClusters.1 hBc).2.1) (subset_univ _)
  rw [ih B hB hBS G, forestDist_eq_sum_entering]
  unfold populationKernel
  rw [ite_eq_right hBu]
  change _ = ∑ F, _ * kingmanTransition (σ.restrictLength S (sub S B)) F G
  unfold SpeciesTree.restrictLength
  rw [marg_filter_top hH hA hB hBS (hbot B hB)]

private theorem marg_prune (σ : SpeciesTree X) {S : Finset X} (hS : S.Nonempty) (s : L → S)
    {A : Finset X} (hA : A ∈ σ.clusters) (hAS : (A ∩ S).Nonempty) (hAu : A ≠ univ) :
    PruneEq σ hS s A := by
  have hH := σ.isHierarchy
  induction A using Finset.strongInduction with
  | H A ih =>
  intro G
  rw [forestDist_eq_sum_entering]
  unfold populationKernel; rw [ite_eq_right hAu]
  by_cases hc : ∃ B₀ ∈ childClusters σ.clusters A, sub S B₀ = sub S A
  · obtain ⟨B₀, hB₀, htr⟩ := hc
    obtain ⟨hB₀H, hB₀A, -⟩ := mem_childClusters.1 hB₀
    have hB₀S : (B₀ ∩ S).Nonempty := subtype_nonempty_iff.1 (htr ▸ subtype_nonempty_iff.2 hAS)
    have hB₀u : B₀ ≠ univ := ssubset_univ_iff.1 (hB₀A.trans_le (subset_univ A))
    have hAB₀ : A ∉ chain σ.clusters S B₀ :=
      fun h => not_subset_of_ssubset hB₀A (mem_filter.1 h).2.1
    rw [marg_filter_chain hH hB₀ htr hAS hA, sum_insert hAB₀]
    simp_rw [marg_enteringDist_chain hH σ.length (fun l => (s l).2) hB₀ htr,
      ih B₀ hB₀A hB₀H hB₀S hB₀u, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun F₀ _ => ?_
    rw [htr, add_comm, kingmanTransition_add, Matrix.mul_apply, mul_sum]
    exact sum_congr rfl fun F _ => by ring
  · push Not at hc
    rw [marg_filter_bot hH hA hc, sum_singleton]
    exact sum_congr rfl fun F _ => by
      rw [marg_enteringDist_restrict σ hS s hA hc (fun B hB hBS =>
        ih B (mem_childClusters.1 hB).2.1 (mem_childClusters.1 hB).1 hBS
          (ssubset_univ_iff.1 ((mem_childClusters.1 hB).2.1.trans_le (subset_univ A)))) F]

theorem SpeciesTree.rootedDist_restrict (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty)
    (s : L → S) (G : Finset (Finset L)) :
    (σ.restrict S hS).rootedDist s G = σ.rootedDist (fun l => (s l : X)) G := by
  have hH := σ.isHierarchy
  have hH' := (σ.restrict S hS).isHierarchy
  unfold SpeciesTree.rootedDist
  have htru : sub S (univ : Finset X) = univ := subtype_univ _
  have hunivS : ((univ : Finset X) ∩ S).Nonempty := by simpa using hS
  rw [forestDist_eq_sum_entering, forestDist_eq_sum_entering]
  unfold populationKernel; rw [ite_eq_left rfl, ite_eq_left rfl]
  by_cases hc : ∃ B₀ ∈ childClusters σ.clusters univ, sub S B₀ = sub S (univ : Finset X)
  · obtain ⟨B₀, hB₀, htr⟩ := hc
    obtain ⟨hB₀H, hB₀A, -⟩ := mem_childClusters.1 hB₀
    have hB₀S : (B₀ ∩ S).Nonempty := subtype_nonempty_iff.1 (htr ▸ subtype_nonempty_iff.2 hunivS)
    symm
    simp_rw [marg_enteringDist_chain hH σ.length (fun l => (s l).2) hB₀ htr,
      marg_prune σ hS s hB₀H hB₀S (ssubset_univ_iff.1 hB₀A), sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun F₀ _ => ?_
    rw [htr, htru]
    by_cases h0 : enteringDist (σ.restrict S hS).clusters (σ.restrict S hS).length s univ F₀ = 0
    · simp only [h0, zero_mul, sum_const_zero]
    · simp_rw [mul_assoc, ← mul_sum]
      rw [kingmanTransition_mul_kingmanAbsorption (enteringDist_support hH' _ s h0)]
  · push Not at hc
    refine sum_congr rfl fun F _ => ?_
    rw [marg_enteringDist_restrict σ hS s σ.univ_mem hc (fun B hB hBS =>
      marg_prune σ hS s (mem_childClusters.1 hB).1 hBS
        (ssubset_univ_iff.1 (mem_childClusters.1 hB).2.1)) F, htru]


private theorem marg_tr_compl (e : L' ↪ L) (A : Finset L) : (tr e A)ᶜ = tr e Aᶜ := by
  ext l; simp

private theorem marg_tr_ne_univ (e : L' ↪ L) {A : Finset L} :
    tr e A ≠ univ ↔ ∃ l, e l ∉ A := by
  simp [Finset.ext_iff]

private theorem marg_unroot_restrictForest (e : L' ↪ L) (G : Finset (Finset L)) :
    unroot (restrictForest e G) = (restrictForest e (unroot G)).erase univ := by
  ext D
  simp only [mem_unroot, mem_erase, marg_mem_restrictForest, ne_eq]
  constructor
  · rintro (⟨⟨A, hA, hAm, rfl⟩, hDu⟩ | ⟨⟨A, hA, ⟨l₁, hl₁⟩, hAD⟩, hDu⟩)
    · obtain ⟨l, hl⟩ := (marg_tr_ne_univ e).1 hDu
      exact ⟨hDu, A, Or.inl ⟨hA, fun h => hl (h ▸ mem_univ _)⟩, hAm, rfl⟩
    · obtain ⟨l₂, hl₂⟩ := (marg_tr_ne_univ e).1 (hAD ▸ hDu)
      exact ⟨by rw [← compl_compl D, ← hAD, marg_tr_compl]; exact (marg_tr_ne_univ e).2 ⟨l₁, by simp [hl₁]⟩,
        Aᶜ, Or.inr ⟨(compl_compl A).symm ▸ hA, fun h => hl₂ ((compl_compl A).symm ▸ h ▸ mem_univ _)⟩,
        ⟨l₂, by simp [hl₂]⟩, by rw [← marg_tr_compl, hAD, compl_compl]⟩
  · rintro ⟨hDu, A, (⟨hA, -⟩ | ⟨hA, -⟩), hAm, rfl⟩
    · exact Or.inl ⟨⟨A, hA, hAm, rfl⟩, hDu⟩
    · obtain ⟨l₁, hl₁⟩ := hAm; obtain ⟨l₂, hl₂⟩ := (marg_tr_ne_univ e).1 hDu
      exact Or.inr ⟨⟨Aᶜ, hA, ⟨l₂, by simp [hl₂]⟩, by rw [← marg_tr_compl]⟩,
        by rw [marg_tr_compl]; exact (marg_tr_ne_univ e).2 ⟨l₁, by simp [hl₁]⟩⟩

theorem SpeciesTree.unrootedDist_comp_embedding (σ : SpeciesTree X) (s : L → X) (e : L' ↪ L)
    (T' : Finset (Finset L')) :
    σ.unrootedDist (s ∘ e) T' =
      ∑ T, if (restrictForest e T).erase univ = T' then σ.unrootedDist s T else 0 := by
  unfold SpeciesTree.unrootedDist
  have hr (G') : σ.rootedDist (s ∘ e) G' =
      ∑ G, if restrictForest e G = G' then σ.rootedDist s G else 0 :=
    forestDist_comp_embedding σ.isHierarchy σ.length s e σ.univ_mem G'
  simp_rw [hr]
  rw [marg_sum_ite_comp (restrictForest e) unroot (σ.rootedDist s) T',
    marg_sum_ite_comp unroot (fun T => (restrictForest e T).erase univ) (σ.rootedDist s) T']
  simp_rw [marg_unroot_restrictForest]


abbrev pre (s : L → X) (A : Finset X) : Finset L := univ.filter (s · ∈ A)

def extendClusters (H : Finset (Finset X)) (s : L → X) : Finset (Finset L) :=
  H.image (pre s) ∪ univ.image ({·})

lemma multi_mem_extendClusters {H : Finset (Finset X)} (s : L → X) {A : Finset X}
    (hA : A ∈ H) : pre s A ∈ extendClusters H s :=
  mem_union_left _ (mem_image_of_mem _ hA)

lemma multi_pre_univ (s : L → X) : pre s univ = univ :=
  filter_true_of_mem fun _ _ => mem_univ _

private lemma multi_pre_singleton (s : L → X) (x : X) :
    pre s {x} = univ.filter fun l => s l = x := by
  simp only [pre, mem_singleton]

lemma multi_pre_mono (s : L → X) {A B : Finset X} (h : A ⊆ B) : pre s A ⊆ pre s B :=
  fun l hl => mem_filter.2 ⟨mem_univ l, h (mem_filter.1 hl).2⟩

private lemma multi_pre_subset_pre {s : L → X} (hs : Function.Surjective s) {A B : Finset X} :
    pre s A ⊆ pre s B ↔ A ⊆ B :=
  ⟨fun h x hx => let ⟨l, hl⟩ := hs x; hl ▸ (mem_filter.1 (h (mem_filter.2 ⟨mem_univ l, hl.symm ▸ hx⟩))).2,
    multi_pre_mono s⟩

private lemma multi_pre_inj {s : L → X} (hs : Function.Surjective s) {A B : Finset X} :
    pre s A = pre s B ↔ A = B :=
  ⟨fun h => subset_antisymm ((multi_pre_subset_pre hs).1 h.le) ((multi_pre_subset_pre hs).1 h.ge),
    fun h => h ▸ rfl⟩

private lemma multi_pre_ssubset_pre {s : L → X} (hs : Function.Surjective s) {A B : Finset X} :
    pre s A ⊂ pre s B ↔ A ⊂ B := by
  rw [ssubset_iff_subset_ne, ssubset_iff_subset_ne, multi_pre_subset_pre hs, Ne, Ne,
    multi_pre_inj hs]

private lemma multi_pre_ne_univ {s : L → X} (hs : Function.Surjective s) {A : Finset X}
    (hA : A ≠ univ) : pre s A ≠ univ :=
  fun h => hA ((multi_pre_inj hs).1 (h.trans (multi_pre_univ s).symm))

lemma multi_pre_nonempty {s : L → X} (hs : Function.Surjective s) {A : Finset X}
    (hA : A.Nonempty) : (pre s A).Nonempty := by
  obtain ⟨x, hx⟩ := hA; obtain ⟨l, rfl⟩ := hs x
  exact ⟨l, mem_filter.2 ⟨mem_univ l, hx⟩⟩

private lemma multi_card_le_card_pre {s : L → X} (hs : Function.Surjective s) (A : Finset X) :
    #A ≤ #(pre s A) :=
  (card_le_card (t := (pre s A).image s) fun x hx =>
    let ⟨l, hl⟩ := hs x; hl ▸ mem_image_of_mem s (mem_filter.2 ⟨mem_univ l, hl.symm ▸ hx⟩)).trans
      card_image_le

private lemma multi_sampledForest_pre (s : L → X) (A : Finset X) :
    sampledForest s A = sampledForest id (pre s A) := by
  unfold sampledForest; congr 1; ext l; simp

noncomputable def SpeciesTree.extendLength (σ : SpeciesTree X) (s : L → X) (B : Finset L) : ℝ :=
  if h : ∃ A ∈ σ.clusters, pre s A = B ∧ 2 ≤ #B then σ.length h.choose else 1

noncomputable def SpeciesTree.extend (σ : SpeciesTree X) (s : L → X)
    (hs : Function.Surjective s) : SpeciesTree L where
  clusters := extendClusters σ.clusters s
  univ_mem := multi_pre_univ s ▸ multi_mem_extendClusters s σ.univ_mem
  singleton_mem l := mem_union_right _ (mem_image_of_mem _ (mem_univ l))
  nonempty_of_mem B hB := by
    rcases mem_union.1 hB with hB | hB
    · obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
      exact multi_pre_nonempty hs (σ.nonempty_of_mem A hA)
    · obtain ⟨l, -, rfl⟩ := mem_image.1 hB
      exact singleton_nonempty l
  laminar B hB C hC := by
    rcases mem_union.1 hB with hB | hB
    · obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
      rcases mem_union.1 hC with hC | hC
      · obtain ⟨A', hA', rfl⟩ := mem_image.1 hC
        rcases σ.laminar A hA A' hA' with h | h | h
        · exact Or.inl (multi_pre_mono s h)
        · exact Or.inr (Or.inl (multi_pre_mono s h))
        · exact Or.inr (Or.inr (disjoint_left.2 fun _ hlA hlB =>
            disjoint_left.1 h (mem_filter.1 hlA).2 (mem_filter.1 hlB).2))
      · obtain ⟨l, -, rfl⟩ := mem_image.1 hC
        rcases singleton_laminar l (pre s A) with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h.symm)
    · obtain ⟨l, -, rfl⟩ := mem_image.1 hB
      exact singleton_laminar l C
  length := σ.extendLength s
  length_pos B _ hBu := by
    unfold SpeciesTree.extendLength
    split_ifs with h
    · obtain ⟨hA, hAB, -⟩ := h.choose_spec
      exact σ.length_pos _ hA fun hu => hBu (by rw [← hAB, hu, multi_pre_univ])
    · exact one_pos

private lemma multi_extendLength_pre (σ : SpeciesTree X) {s : L → X}
    (hs : Function.Surjective s) {A : Finset X} (hA : A ∈ σ.clusters) (h2 : 2 ≤ #(pre s A)) :
    σ.extendLength s (pre s A) = σ.length A := by
  unfold SpeciesTree.extendLength
  have h : ∃ A' ∈ σ.clusters, pre s A' = pre s A ∧ 2 ≤ #(pre s A) := ⟨A, hA, rfl, h2⟩
  rw [dite_eq_left h, (multi_pre_inj hs).1 h.choose_spec.2.1]

private lemma multi_populationKernel_pre (σ : SpeciesTree X) {s : L → X}
    (hs : Function.Surjective s) {A : Finset X} (hA : A ∈ σ.clusters) (h2 : 2 ≤ #(pre s A)) :
    populationKernel (L := L) σ.length A = populationKernel (σ.extendLength s) (pre s A) := by
  unfold populationKernel
  by_cases hAu : A = univ
  · subst hAu; rw [ite_eq_left rfl, ite_eq_left (multi_pre_univ s)]
  · rw [ite_eq_right hAu, ite_eq_right (multi_pre_ne_univ hs hAu),
      multi_extendLength_pre σ hs hA h2]

private lemma multi_childClusters_pre (σ : SpeciesTree X) {s : L → X}
    (hs : Function.Surjective s) {A : Finset X} (h2 : 2 ≤ #A) :
    childClusters (extendClusters σ.clusters s) (pre s A) =
      (childClusters σ.clusters A).image (pre s) := by
  ext C
  rw [mem_image]
  constructor
  · intro hC
    obtain ⟨hCE, hCA, hmax⟩ := mem_childClusters.1 hC
    rcases mem_union.1 hCE with hCE | hCE
    · obtain ⟨D, hD, rfl⟩ := mem_image.1 hCE
      exact ⟨D, mem_childClusters.2 ⟨hD, (multi_pre_ssubset_pre hs).1 hCA,
        fun D' hD' hDD' hD'A => hmax _ (multi_mem_extendClusters s hD')
          ((multi_pre_ssubset_pre hs).2 hDD') ((multi_pre_ssubset_pre hs).2 hD'A)⟩, rfl⟩
    · obtain ⟨l, -, rfl⟩ := mem_image.1 hCE
      have hl : s l ∈ A := (mem_filter.1 (hCA.subset (mem_singleton_self l))).2
      obtain ⟨B, hB, hlB⟩ := σ.isHierarchy.exists_mem_childClusters h2 hl
      refine ⟨B, hB, ?_⟩
      rcases (singleton_subset_iff.2 (mem_filter.2 ⟨mem_univ _, hlB⟩) : {l} ⊆ pre s B).eq_or_ssubset
        with h | h
      · exact h.symm
      · exact absurd ((multi_pre_ssubset_pre hs).2 (mem_childClusters.1 hB).2.1)
          (hmax _ (multi_mem_extendClusters s (mem_childClusters.1 hB).1) h)
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨hBH, hBA, hmax⟩ := mem_childClusters.1 hB
    refine mem_childClusters.2 ⟨multi_mem_extendClusters s hBH, (multi_pre_ssubset_pre hs).2 hBA,
      fun C hC hBC hCA => ?_⟩
    rcases mem_union.1 hC with hC | hC
    · obtain ⟨D, hD, rfl⟩ := mem_image.1 hC
      exact hmax D hD ((multi_pre_ssubset_pre hs).1 hBC) ((multi_pre_ssubset_pre hs).1 hCA)
    · obtain ⟨l, -, rfl⟩ := mem_image.1 hC
      exact (multi_pre_nonempty hs (σ.nonempty_of_mem B hBH)).ne_empty
        (ssubset_singleton_iff.1 hBC)

private lemma multi_sum_pi_equiv {ι κ α : Type*} [Fintype α] [DecidableEq ι] [DecidableEq κ]
    {S : Finset ι} {T : Finset κ} (e : S ≃ T) (g : (T → α) → ℝ) :
    ∑ f : T → α, g f = ∑ f : S → α, g (fun C => f (e.symm C)) :=
  (Fintype.sum_equiv (e.arrowCongr (Equiv.refl α)) _ _ fun _ => rfl).symm

private lemma multi_forestDist_extend (σ : SpeciesTree X) {s : L → X}
    (hs : Function.Surjective s) (h2 : ∀ x, #(univ.filter fun l => s l = x) ≤ 2) {A : Finset X}
    (hA : A ∈ σ.clusters) (G : Finset (Finset L)) :
    forestDist σ.clusters σ.length s A G =
      forestDist (extendClusters σ.clusters s) (σ.extendLength s) id (pre s A) G := by
  have hE : IsHierarchy (extendClusters σ.clusters s) := (σ.extend s hs).isHierarchy
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  obtain ⟨x, hx⟩ := σ.nonempty_of_mem A hA
  rcases Nat.lt_or_ge 1 #A with hA2 | hA1
  · have hpre2 : 2 ≤ #(pre s A) := (show 2 ≤ #A from hA2).trans (multi_card_le_card_pre hs A)
    have hch := multi_childClusters_pre σ hs (show 2 ≤ #A from hA2)
    let e : childClusters σ.clusters A ≃
        childClusters (extendClusters σ.clusters s) (pre s A) :=
      Equiv.ofBijective (fun B => ⟨_, hch ▸ mem_image_of_mem _ B.2⟩)
        ⟨fun B B' h => Subtype.ext ((multi_pre_inj hs).1 (congrArg Subtype.val h)), fun C => by
          have hC : (C : Finset L) ∈ (childClusters σ.clusters A).image (pre s) := by
            rw [← hch]; exact C.2
          obtain ⟨B, hB, hBC⟩ := mem_image.1 hC
          exact ⟨⟨B, hB⟩, Subtype.ext hBC⟩⟩
    rw [forestDist.eq_1 σ.clusters σ.length, forestDist.eq_1 (extendClusters σ.clusters s),
      multi_sum_pi_equiv e]
    refine Finset.sum_congr rfl fun g _ => ?_
    congr 1
    · refine Fintype.prod_equiv e _ _ fun B => ?_
      dsimp only
      rw [e.symm_apply_apply, ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1]
      rfl
    · rw [multi_populationKernel_pre σ hs hA hpre2, multi_sampledForest_pre s A]
      congr 2
      refine le_antisymm (Finset.sup_le fun B _ => ?_) (Finset.sup_le fun C _ => Finset.le_sup (mem_univ _))
      have := Finset.le_sup (f := fun C => g (e.symm C)) (mem_univ (e B))
      simpa using this
  · have hAx : A = {x} :=
      eq_singleton_iff_unique_mem.2 ⟨hx, fun y hy => card_le_one.1 hA1 y hy x hx⟩
    subst hAx
    have hx1 : 1 ≤ #(univ.filter fun l => s l = x) := by
      obtain ⟨l, hl⟩ := hs x
      exact card_pos.2 ⟨l, mem_filter.2 ⟨mem_univ l, hl⟩⟩
    rcases (show #(univ.filter fun l => s l = x) = 1 ∨ #(univ.filter fun l => s l = x) = 2 by
      have := h2 x; omega) with h1 | h2'
    · obtain ⟨l, hl⟩ := card_eq_one.1 h1
      rw [forestDist_singleton_of_card_le_one σ.isHierarchy σ.length h1.le,
        multi_pre_singleton, hl, forestDist_id_singleton hE, multi_sampledForest_pre s {x},
        multi_pre_singleton, hl]
      congr 2; ext C; simp [sampledForest, eq_comm]
    · rw [forestDist_of_childClusters_eq_empty (σ.isHierarchy.childClusters_singleton x),
        multi_populationKernel_pre σ hs hA (by rw [multi_pre_singleton]; omega),
        multi_sampledForest_pre s {x}, multi_pre_singleton, forestDist.eq_1]
      have hB1 : ∀ B : childClusters (extendClusters σ.clusters s) (univ.filter fun l => s l = x),
          ∃ l ∈ univ.filter fun l => s l = x, (B : Finset L) = {l} := fun B => by
        obtain ⟨hBE, hBS, -⟩ := mem_childClusters.1 B.2
        have h1 := (hE.2.2.1 B hBE).card_pos
        have h2 := card_lt_card hBS
        obtain ⟨l, hl⟩ := card_eq_one.1 (by omega : #(B : Finset L) = 1)
        exact ⟨l, hBS.subset (hl ▸ mem_singleton_self l), hl⟩
      have hf0 : ∀ B : childClusters (extendClusters σ.clusters s) (univ.filter fun l => s l = x),
          ∀ F, forestDist (extendClusters σ.clusters s) (σ.extendLength s) id B F =
            if F = {(B : Finset L)} then 1 else 0 := fun B F => by
        obtain ⟨l, -, hl⟩ := hB1 B; rw [hl, forestDist_id_singleton hE]
      symm
      refine (Fintype.sum_eq_single (fun B => ({B.1} : Finset (Finset L))) fun f hf => ?_).trans ?_
      · obtain ⟨B, hBf⟩ := Function.ne_iff.1 hf
        rw [Finset.prod_eq_zero (mem_univ B) (by rw [hf0, ite_eq_right hBf]), zero_mul]
      · dsimp only
        rw [Finset.prod_eq_one fun B _ => by rw [hf0, ite_eq_left rfl], one_mul,
          union_eq_right.2 (Finset.sup_le fun B _ C hC => by
            obtain ⟨l, hlS, hl⟩ := hB1 B
            rw [mem_singleton.1 hC, hl, singleton_mem_sampledForest]; exact hlS)]

theorem SpeciesTree.rootedDist_extend (σ : SpeciesTree X) {s : L → X}
    (hs : Function.Surjective s) (h2 : ∀ x, #(univ.filter fun l => s l = x) ≤ 2)
    (G : Finset (Finset L)) :
    σ.rootedDist s G = (σ.extend s hs).rootedDist id G := by
  unfold SpeciesTree.rootedDist
  rw [multi_forestDist_extend σ hs h2 σ.univ_mem G, multi_pre_univ]
  rfl

theorem SpeciesTree.sameRootedMetricTree_of_extend (hX : 2 ≤ Fintype.card X)
    (σ σ' : SpeciesTree X) {s : L → X} (hs : Function.Surjective s)
    (h : (σ.extend s hs).SameRootedMetricTree (σ'.extend s hs)) :
    σ.SameRootedMetricTree σ' ∧
      ∀ x, 2 ≤ #(univ.filter fun l => s l = x) → σ.length {x} = σ'.length {x} := by
  obtain ⟨hcl, hlen⟩ := h
  change extendClusters σ.clusters s = extendClusters σ'.clusters s at hcl
  have hmem : ∀ {τ τ' : SpeciesTree X}, extendClusters τ.clusters s = extendClusters τ'.clusters s →
      ∀ A ∈ τ.clusters, A ∈ τ'.clusters := by
    intro τ τ' hcl A hA
    have hA' : pre s A ∈ extendClusters τ'.clusters s := hcl ▸ multi_mem_extendClusters s hA
    rcases mem_union.1 hA' with h | h
    · obtain ⟨A', hA', hA'A⟩ := mem_image.1 h
      rwa [(multi_pre_inj hs).1 hA'A] at hA'
    · obtain ⟨l, -, hl⟩ := mem_image.1 h
      have hAs : A = {s l} := by
        ext y; rw [mem_singleton]
        refine ⟨fun hy => ?_, fun hy => ?_⟩
        · obtain ⟨l', rfl⟩ := hs y
          exact congrArg s (mem_singleton.1 (hl ▸ mem_filter.2 ⟨mem_univ l', hy⟩))
        · subst hy
          have hlA : l ∈ pre s A := hl ▸ mem_singleton_self l
          exact (mem_filter.1 hlA).2
      exact hAs ▸ τ'.singleton_mem _
  have hcl' : σ.clusters = σ'.clusters :=
    subset_antisymm (fun A hA => hmem hcl A hA) (fun A hA => hmem hcl.symm A hA)
  have key : ∀ A ∈ σ.clusters, 2 ≤ #(pre s A) → A ≠ univ → σ.length A = σ'.length A := by
    intro A hA h2 hAu
    have := hlen _ (multi_mem_extendClusters s hA) h2 (multi_pre_ne_univ hs hAu)
    change σ.extendLength s _ = σ'.extendLength s _ at this
    rwa [multi_extendLength_pre σ hs hA h2, multi_extendLength_pre σ' hs (hcl' ▸ hA) h2] at this
  refine ⟨⟨hcl', fun A hA hA2 hAu => key A hA (hA2.trans (multi_card_le_card_pre hs A)) hAu⟩,
    fun x hx => key {x} (σ.singleton_mem x) (by rwa [multi_pre_singleton]) fun hxu => ?_⟩
  have := congrArg card hxu
  rw [card_singleton, card_univ] at this
  omega


end ADR11
