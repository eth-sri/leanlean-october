module

public import ADR11.MSC.Basic

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {L : Type*} [Fintype L] [DecidableEq L] {L' : Type*} [Fintype L'] [DecidableEq L']

abbrev pre (s : L → X) (A : Finset X) : Finset L := univ.filter fun l => s l ∈ A

abbrev tr (e : L' ↪ L) (A : Finset L) : Finset L' := pre e A

def restrictForest (e : L' ↪ L) (F : Finset (Finset L)) : Finset (Finset L') :=
  (F.filter fun A => ∃ l, e l ∈ A).image (tr e)

/-! ### Restricting forests -/

omit [Fintype L] in
private theorem marg_mem_restrictForest (e : L' ↪ L) {F : Finset (Finset L)} {D : Finset L'} :
    D ∈ restrictForest e F ↔ ∃ A ∈ F, (∃ l, e l ∈ A) ∧ tr e A = D := by
  unfold restrictForest; simp only [mem_image, mem_filter, and_assoc]

omit [Fintype L] in
private theorem marg_tr_mem_restrictForest (e : L' ↪ L) {F : Finset (Finset L)} {A : Finset L}
    (hA : A ∈ F) (hmeet : ∃ l, e l ∈ A) : tr e A ∈ restrictForest e F :=
  (marg_mem_restrictForest e).2 ⟨A, hA, hmeet, rfl⟩

omit [Fintype X] [DecidableEq L] in
private theorem marg_tr_mono (s : L → X) {A B : Finset X} (h : A ⊆ B) : pre s A ⊆ pre s B :=
  fun l hl => mem_filter.2 ⟨mem_univ l, h (mem_filter.1 hl).2⟩

omit [Fintype X] [DecidableEq L] in
private theorem marg_tr_disjoint (s : L → X) {A B : Finset X} (h : Disjoint A B) :
    Disjoint (pre s A) (pre s B) :=
  disjoint_left.2 fun _ hlA hlB => disjoint_left.1 h (mem_filter.1 hlA).2 (mem_filter.1 hlB).2

omit [Fintype L] [DecidableEq L'] in
private theorem marg_tr_eq_empty (e : L' ↪ L) {A : Finset L} (h : ¬ ∃ l, e l ∈ A) :
    tr e A = ∅ := by
  ext l; simp only [tr, mem_filter, mem_univ, true_and, notMem_empty, iff_false]
  exact fun hl => h ⟨l, hl⟩

omit [Fintype L] in
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
    · exact Or.inr (Or.inr (marg_tr_disjoint e h))

omit [DecidableEq L'] in
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
  · rintro ⟨A, hA, ⟨l, hl⟩, rfl⟩
    refine mem_roots.2 ⟨marg_tr_mem_restrictForest e (roots_subset F hA) ⟨l, hl⟩, fun D hD hAD => ?_⟩
    obtain ⟨B, hB, -, rfl⟩ := (marg_mem_restrictForest e).1 hD
    obtain ⟨R, hR, hBR⟩ := exists_mem_roots_subset hB
    have hlB : e l ∈ B := (mem_filter.1 (hAD (mem_filter.2 ⟨mem_univ l, hl⟩))).2
    have hAR : A = R := hF.eq_of_mem_roots_of_mem hA hR hl (hBR hlB)
    exact subset_antisymm (marg_tr_mono e (hAR ▸ hBR)) hAD

private theorem marg_restrictForest_merge {F : Finset (Finset L)} (e : L' ↪ L)
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) :
    restrictForest e (insert (A ∪ B) F) =
      if (∃ l, e l ∈ A) ∧ (∃ l, e l ∈ B) then insert (tr e A ∪ tr e B) (restrictForest e F)
      else restrictForest e F := by
  have hins : restrictForest e (insert (A ∪ B) F) =
      if ∃ l, e l ∈ A ∪ B then insert (tr e (A ∪ B)) (restrictForest e F)
      else restrictForest e F := by
    unfold restrictForest; rw [filter_insert]; split_ifs <;> simp [image_insert]
  have hun : tr e (A ∪ B) = tr e A ∪ tr e B := by ext l; simp [tr]
  rw [hins, hun]
  by_cases hAm : ∃ l, e l ∈ A <;> by_cases hBm : ∃ l, e l ∈ B
  · have hU : ∃ l, e l ∈ A ∪ B := let ⟨l, hl⟩ := hAm; ⟨l, mem_union_left _ hl⟩
    rw [ite_eq_left hU, ite_eq_left ⟨hAm, hBm⟩]
  · have hU : ∃ l, e l ∈ A ∪ B := let ⟨l, hl⟩ := hAm; ⟨l, mem_union_left _ hl⟩
    rw [ite_eq_left hU, ite_eq_right (fun h => hBm h.2), marg_tr_eq_empty e hBm, union_empty]
    exact insert_eq_of_mem (marg_tr_mem_restrictForest e (roots_subset F hA) hAm)
  · have hU : ∃ l, e l ∈ A ∪ B := let ⟨l, hl⟩ := hBm; ⟨l, mem_union_right _ hl⟩
    rw [ite_eq_left hU, ite_eq_right (fun h => hAm h.1), marg_tr_eq_empty e hAm, empty_union]
    exact insert_eq_of_mem (marg_tr_mem_restrictForest e (roots_subset F hB) hBm)
  · have hU : ¬ ∃ l, e l ∈ A ∪ B := fun ⟨l, hl⟩ =>
      (mem_union.1 hl).elim (fun h => hAm ⟨l, h⟩) (fun h => hBm ⟨l, h⟩)
    rw [ite_eq_right hU, ite_eq_right (fun h => hAm h.1)]

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
    · rw [ite_eq_right h] at hne; exact absurd rfl hne
  · rintro ⟨A, hA, B, hB, hAB, hAm, hBm, rfl⟩
    refine ⟨mem_merges.2 ⟨A, hA, B, hB, hAB, rfl⟩, ?_⟩
    rw [marg_restrictForest_merge e hA hB, ite_eq_left ⟨hAm, hBm⟩]
    exact fun h => union_not_mem_of_mem_roots
      ((marg_mem_roots_restrictForest hF e).2 ⟨A, hA, hAm, rfl⟩)
      ((marg_mem_roots_restrictForest hF e).2 ⟨B, hB, hBm, rfl⟩)
      (fun h' => hAB (marg_tr_inj hF e hA hB hAm h')) (h ▸ mem_insert_self _ _)

private theorem marg_sum_merges {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L)
    (u : Finset (Finset L') → ℝ) :
    -((#(roots F)).choose 2 : ℝ) * u (restrictForest e F) +
        ∑ H ∈ merges F, u (restrictForest e H) =
      -((#(roots (restrictForest e F))).choose 2 : ℝ) * u (restrictForest e F) +
        ∑ H' ∈ merges (restrictForest e F), u H' := by
  set rF := restrictForest e F with hrF
  have hrFf : IsForest rF := hF.restrictForest e
  set M₂ := (merges F).filter fun H => restrictForest e H ≠ rF
  have himage : M₂.image (restrictForest e) = merges rF := by
    ext H'; rw [mem_image]
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
    have hr := fun {A} (hA : A ∈ roots F) (hAm : ∃ l, e l ∈ A) =>
      (marg_mem_roots_restrictForest hF e).2 ⟨A, hA, hAm, rfl⟩
    rcases (hrFf.merge_eq_iff (hr hA₁ hA₁m) (hr hB₁ hB₁m)
        (fun h' => hAB₁ (marg_tr_inj hF e hA₁ hB₁ hA₁m h'))
        (hr hA₂ hA₂m) (hr hB₂ hB₂m)
        (fun h' => hAB₂ (marg_tr_inj hF e hA₂ hB₂ hA₂m h'))).1 h12 with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [marg_tr_inj hF e hA₁ hA₂ hA₁m h1, marg_tr_inj hF e hB₁ hB₂ hB₁m h2]
    · rw [marg_tr_inj hF e hA₁ hB₂ hA₁m h1, marg_tr_inj hF e hB₁ hA₂ hB₁m h2, union_comm]
  have hsub : ∑ H ∈ merges F, (u (restrictForest e H) - u rF) =
      ∑ H' ∈ merges rF, (u H' - u rF) := by
    rw [← himage, sum_image hinj]
    refine (sum_subset (filter_subset _ _) fun H hH hnot => ?_).symm
    simp only [mem_filter, hH, true_and, not_not] at hnot
    rw [hnot, sub_self]
  simp only [sum_sub_distrib, sum_const, hF.card_merges, hrFf.card_merges, nsmul_eq_mul] at hsub
  linarith

private theorem marg_kingmanGenerator_ne_zero {F G : Finset (Finset L)} (hF : IsForest F)
    (h : kingmanGenerator F G ≠ 0) : IsForest G := by
  rw [kingmanGenerator_apply_of_isForest] at h
  split_ifs at h with h1 h2
  · exact h1 ▸ hF
  · exact (hF.of_mem_merges h2).1
  · exact absurd rfl h

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
    have hstep : ∀ H : Finset (Finset L), kingmanGenerator F H *
        ∑ G, (kingmanGenerator ^ n) H G * w (restrictForest e G) =
          kingmanGenerator F H * u (restrictForest e H) := fun H => by
      by_cases hQ : kingmanGenerator F H = 0
      · rw [hQ, zero_mul, zero_mul]
      · rw [ih (marg_kingmanGenerator_ne_zero hF hQ) w]
    calc ∑ G, (kingmanGenerator ^ (n + 1)) F G * w (restrictForest e G)
        = ∑ H, kingmanGenerator F H *
            ∑ G, (kingmanGenerator ^ n) H G * w (restrictForest e G) := by
          simp_rw [pow_succ', Matrix.mul_apply, sum_mul]
          rw [sum_comm]
          simp_rw [mul_sum, mul_assoc]
      _ = ∑ H, kingmanGenerator F H * u (restrictForest e H) := sum_congr rfl fun H _ => hstep H
      _ = ∑ H', kingmanGenerator (restrictForest e F) H' * u H' := by
          rw [hF.sum_kingmanGenerator_mul (fun G => u (restrictForest e G)),
            (hF.restrictForest e).sum_kingmanGenerator_mul u]
          exact marg_sum_merges hF e u
      _ = ∑ G', (kingmanGenerator ^ (n + 1)) (restrictForest e F) G' * w G' := by
          simp_rw [hu, pow_succ', Matrix.mul_apply, sum_mul, mul_sum, mul_assoc]
          rw [sum_comm]

private theorem marg_sum_kingmanTransition {F : Finset (Finset L)} (hF : IsForest F)
    (e : L' ↪ L) (t : ℝ) (w : Finset (Finset L') → ℝ) :
    ∑ G, kingmanTransition t F G * w (restrictForest e G) =
      ∑ G', kingmanTransition t (restrictForest e F) G' * w G' := by
  have h1 : HasSum (fun n : ℕ => ∑ G, ((n.factorial : ℝ))⁻¹ *
      ((t • kingmanGenerator (L := L)) ^ n) F G * w (restrictForest e G))
      (∑ G, kingmanTransition t F G * w (restrictForest e G)) :=
    hasSum_sum fun G _ => (fact_hasSum_exp_apply _ F G).mul_right _
  have h2 : HasSum (fun n : ℕ => ∑ G', ((n.factorial : ℝ))⁻¹ *
      ((t • kingmanGenerator (L := L')) ^ n) (restrictForest e F) G' * w G')
      (∑ G', kingmanTransition t (restrictForest e F) G' * w G') :=
    hasSum_sum fun G' _ => (fact_hasSum_exp_apply _ _ G').mul_right _
  refine h1.unique ?_
  convert h2 using 1
  funext n
  simp_rw [smul_pow, Matrix.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum]
  rw [marg_sum_kingmanGenerator_pow e n hF w]

theorem kingmanTransition_lump {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L) (t : ℝ)
    (G' : Finset (Finset L')) :
    ∑ G, (if restrictForest e G = G' then kingmanTransition t F G else 0) =
      kingmanTransition t (restrictForest e F) G' := by
  simpa only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true] using
    marg_sum_kingmanTransition hF e t fun G'' => if G'' = G' then 1 else 0

theorem kingmanAbsorption_lump {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L)
    (G' : Finset (Finset L')) :
    ∑ G, (if restrictForest e G = G' then kingmanAbsorption F G else 0) =
      kingmanAbsorption (restrictForest e F) G' := by
  have h1 : Filter.Tendsto
      (fun t => ∑ G, (if restrictForest e G = G' then kingmanTransition t F G else 0))
      Filter.atTop
      (nhds (∑ G, (if restrictForest e G = G' then kingmanAbsorption F G else 0))) :=
    tendsto_finsetSum _ fun G _ => by
      split_ifs
      · exact tendsto_kingmanTransition hF G
      · exact tendsto_const_nhds
  simp_rw [kingmanTransition_lump hF e] at h1
  exact tendsto_nhds_unique h1 (tendsto_kingmanTransition (hF.restrictForest e) G')

/-! ### Dropping lineages -/

omit [Fintype L] in
private theorem marg_restrictForest_union (e : L' ↪ L) (F₁ F₂ : Finset (Finset L)) :
    restrictForest e (F₁ ∪ F₂) = restrictForest e F₁ ∪ restrictForest e F₂ := by
  unfold restrictForest; rw [filter_union, image_union]

omit [Fintype L] in
private theorem marg_restrictForest_sup {ι : Type*} (e : L' ↪ L) (T : Finset ι)
    (f : ι → Finset (Finset L)) :
    restrictForest e (T.sup f) = T.sup fun i => restrictForest e (f i) :=
  Finset.apply_sup_eq_sup_comp (restrictForest e) (marg_restrictForest_union e)
    (by simp [restrictForest])

private theorem marg_sum_ite_comp {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [DecidableEq γ] (f : α → β) (g : β → γ) (p : α → ℝ) (c : γ) :
    ∑ b, (if g b = c then ∑ a, (if f a = b then p a else 0) else 0) =
      ∑ a, if g (f a) = c then p a else 0 := by
  have h : ∀ b, (if g b = c then ∑ a, (if f a = b then p a else 0) else 0) =
      ∑ a, if f a = b then (if g b = c then p a else 0) else 0 := fun b => by
    split_ifs <;> simp
  simp_rw [h]; rw [sum_comm]
  exact sum_congr rfl fun a _ => by rw [sum_ite_eq]; simp

theorem forestDist_comp_embedding {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) (s : L → X) (e : L' ↪ L) {A : Finset X} (hA : A ∈ H)
    (G' : Finset (Finset L')) :
    forestDist H len (s ∘ e) A G' =
      ∑ G, if restrictForest e G = G' then forestDist H len s A G else 0 := by
  induction A using Finset.strongInduction generalizing G' with
  | H A ih =>
  have hent : ∀ F', enteringDist H len (s ∘ e) A F' =
      ∑ F, if restrictForest e F = F' then enteringDist H len s A F else 0 := fun F' => by
    unfold enteringDist
    rw [marg_sum_ite_comp (fun f : childClusters H A → Finset (Finset L) =>
        univ.sup f ∪ sampledForest s A) (restrictForest e)]
    have hP : ∀ f' : childClusters H A → Finset (Finset L'),
        ∏ B : childClusters H A, forestDist H len (s ∘ e) B (f' B) =
          ∑ f : childClusters H A → Finset (Finset L),
            if (fun B => restrictForest e (f B)) = f' then
              ∏ B : childClusters H A, forestDist H len s B (f B) else 0 := fun f' => by
      rw [(prod_congr rfl fun B _ =>
          ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1 (f' B) :
        ∏ B : childClusters H A, forestDist H len (s ∘ e) B (f' B) =
          ∏ B : childClusters H A, ∑ G, if restrictForest e G = f' B then forestDist H len s B G else 0),
        Fintype.prod_sum]
      exact sum_congr rfl fun f _ => by rw [prod_ite_zero]; simp [funext_iff]
    simp_rw [hP]
    rw [marg_sum_ite_comp (fun f : childClusters H A → Finset (Finset L) =>
        fun B => restrictForest e (f B)) (fun f' => univ.sup f' ∪ sampledForest (s ∘ e) A)]
    have hSF : restrictForest e (sampledForest s A) = sampledForest (s ∘ e) A := by
      ext D; rw [marg_mem_restrictForest, mem_sampledForest]
      constructor
      · rintro ⟨_, hC, ⟨l', hl'⟩, rfl⟩
        obtain ⟨l, hl, rfl⟩ := mem_sampledForest.1 hC
        rw [mem_singleton] at hl'; subst hl'
        exact ⟨l', hl, by ext m; simp [tr, e.injective.eq_iff, eq_comm]⟩
      · rintro ⟨l', hl', rfl⟩
        exact ⟨{e l'}, mem_sampledForest.2 ⟨e l', hl', rfl⟩, ⟨l', mem_singleton_self _⟩,
          by ext m; simp [tr, e.injective.eq_iff]⟩
    exact sum_congr rfl fun f _ => by
      rw [marg_restrictForest_union, marg_restrictForest_sup, hSF]
  have hK : ∀ F, enteringDist H len s A F * ∑ G, (if restrictForest e G = G' then
      populationKernel len A F G else 0) =
        enteringDist H len s A F * populationKernel len A (restrictForest e F) G' := fun F => by
    by_cases h0 : enteringDist H len s A F = 0
    · rw [h0, zero_mul, zero_mul]
    · have hF := (enteringDist_support hH len s h0).1
      unfold populationKernel
      split_ifs
      · rw [kingmanAbsorption_lump hF e G']
      · rw [kingmanTransition_lump hF e _ G']
  calc forestDist H len (s ∘ e) A G'
      = ∑ F', enteringDist H len (s ∘ e) A F' * populationKernel len A F' G' :=
        forestDist_eq_sum_entering H len (s ∘ e) A G'
    _ = ∑ F', ∑ F, if restrictForest e F = F' then
          enteringDist H len s A F * populationKernel len A F' G' else 0 := by
        simp_rw [hent, sum_mul, ite_mul, zero_mul]
    _ = ∑ F, enteringDist H len s A F * populationKernel len A (restrictForest e F) G' := by
        rw [sum_comm]
        exact sum_congr rfl fun F _ => by rw [sum_ite_eq]; simp
    _ = ∑ F, enteringDist H len s A F * ∑ G, (if restrictForest e G = G' then
          populationKernel len A F G else 0) := (sum_congr rfl fun F _ => hK F).symm
    _ = ∑ G, if restrictForest e G = G' then forestDist H len s A G else 0 := by
        simp_rw [mul_sum, mul_ite, mul_zero]
        rw [sum_comm]
        refine sum_congr rfl fun G _ => ?_
        rw [forestDist_eq_sum_entering H len s A G]
        split_ifs <;> simp

theorem SpeciesTree.rootedDist_comp_embedding (σ : SpeciesTree X) (s : L → X) (e : L' ↪ L)
    (G' : Finset (Finset L')) :
    σ.rootedDist (s ∘ e) G' = ∑ G, if restrictForest e G = G' then σ.rootedDist s G else 0 :=
  forestDist_comp_embedding σ.isHierarchy σ.length s e σ.univ_mem G'

/-! ### Pruning the species tree -/

private theorem marg_subtype_mem_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {S A B : Finset X} (hA : A ∈ H) (hB : B ∈ childClusters H A) (hBS : (B ∩ S).Nonempty)
    (hne : B.subtype (· ∈ S) ≠ A.subtype (· ∈ S)) :
    B.subtype (· ∈ S) ∈ childClusters (restrictClusters S H) (A.subtype (· ∈ S)) := by
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

private theorem marg_forestDist_eq_empty {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) {s : L → X} {B : Finset X} (hB : B ∈ H) (hs : ∀ l, s l ∉ B)
    (G : Finset (Finset L)) : forestDist H len s B G = if G = ∅ then 1 else 0 := by
  have hz : ∀ G : Finset (Finset L), G ≠ ∅ → forestDist H len s B G = 0 := fun G hG =>
    by_contra fun h => by
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
    (hB₀ : B₀ ∈ childClusters H A) (htr : B₀.subtype (· ∈ S) = A.subtype (· ∈ S))
    (F : Finset (Finset L)) : enteringDist H len s A F = forestDist H len s B₀ F := by
  have hmem : ∀ l, s l ∈ A ↔ s l ∈ B₀ := fun l => by
    simpa [mem_subtype] using congrArg (⟨s l, hs l⟩ ∈ ·) htr.symm
  have hSF : sampledForest s A = sampledForest s B₀ := by simp only [sampledForest, hmem]
  let b₀ : childClusters H A := ⟨B₀, hB₀⟩
  have hother : ∀ B : childClusters H A, B ≠ b₀ → ∀ G,
      forestDist H len s B G = if G = ∅ then 1 else 0 := fun B hne =>
    marg_forestDist_eq_empty hH len (mem_childClusters.1 B.2).1 fun l hl =>
      Finset.disjoint_left.1 (hH.disjoint_of_mem_childClusters B.2 hB₀ (Subtype.coe_ne_coe.2 hne))
        hl ((hmem l).1 ((mem_childClusters.1 B.2).2.1.subset hl))
  have hsup : ∀ g : childClusters H A → Finset (Finset L),
      (∀ B ≠ b₀, g B = ∅) → univ.sup g = g b₀ := fun g hg =>
    le_antisymm (Finset.sup_le fun B _ => by
      by_cases hB : B = b₀
      · rw [hB]
      · rw [hg B hB]; exact bot_le) (le_sup (mem_univ b₀))
  unfold enteringDist
  let f₀ : childClusters H A → Finset (Finset L) := fun B => if B = b₀ then F else ∅
  rw [Finset.sum_eq_single f₀]
  · have hprod : (∏ B : childClusters H A, forestDist H len s B (f₀ B)) =
        forestDist H len s B₀ F := by
      rw [Finset.prod_eq_single b₀ (fun B _ hne => by simp [f₀, hne, hother B hne]) (by simp)]
      simp [f₀, b₀]
    rw [hsup f₀ (fun B hB => ite_eq_right hB), hprod, hSF]
    simp only [f₀, ↓reduceIte]
    by_cases h0 : forestDist H len s B₀ F = 0
    · simp [h0]
    · rw [union_eq_left.2 (forestDist_support hH len s (mem_childClusters.1 hB₀).1 h0).2.1,
        ite_eq_left rfl]
  · intro f _ hf
    by_cases hemp : ∀ B ≠ b₀, f B = ∅
    · rw [hsup f hemp, hSF]
      by_cases h0 : forestDist H len s B₀ (f b₀) = 0
      · rw [prod_eq_zero (mem_univ b₀) h0, ite_self]
      · rw [union_eq_left.2 (forestDist_support hH len s (mem_childClusters.1 hB₀).1 h0).2.1,
          ite_eq_right fun h => hf (funext fun B => by
            by_cases hB : B = b₀
            · subst hB; simp [f₀, h]
            · simp [f₀, hB, hemp B hB])]
    · push Not at hemp; obtain ⟨B, hB, hne⟩ := hemp
      rw [prod_eq_zero (mem_univ B) (by rw [hother B hB, ite_eq_right hne.ne_empty]), ite_self]
  · simp

private theorem marg_enteringDist_restrict (σ : SpeciesTree X) {S : Finset X} (hS : S.Nonempty)
    (s : L → S) {A : Finset X} (hA : A ∈ σ.clusters)
    (hbot : ∀ B ∈ childClusters σ.clusters A, B.subtype (· ∈ S) ≠ A.subtype (· ∈ S))
    (ih : ∀ B ∈ childClusters σ.clusters A, (B ∩ S).Nonempty → ∀ G,
      forestDist σ.clusters σ.length (fun l => (s l : X)) B G =
        ∑ F, enteringDist (σ.restrict S hS).clusters (σ.restrict S hS).length s
            (B.subtype (· ∈ S)) F *
          kingmanTransition (∑ A' ∈ σ.clusters with A' ⊆ B ∧
            A'.subtype (· ∈ S) = B.subtype (· ∈ S), σ.length A') F G)
    (F : Finset (Finset L)) :
    enteringDist σ.clusters σ.length (fun l => (s l : X)) A F =
      enteringDist (σ.restrict S hS).clusters (σ.restrict S hS).length s
        (A.subtype (· ∈ S)) F := by
  have hH := σ.isHierarchy
  have hH' : IsHierarchy (restrictClusters S σ.clusters) := (σ.restrict S hS).isHierarchy
  have hSF : sampledForest (fun l => (s l : X)) A = sampledForest s (A.subtype (· ∈ S)) := by
    unfold sampledForest; congr 1; ext l; simp [mem_subtype]
  unfold enteringDist
  rw [hSF]
  set T := childClusters σ.clusters A
  set T' := childClusters (σ.restrict S hS).clusters (A.subtype (· ∈ S))
  let P : Finset X → Prop := fun B => (B ∩ S).Nonempty
  let τ : Finset X → Finset S := fun B => B.subtype (· ∈ S)
  let φ := forestDist σ.clusters σ.length (fun l => (s l : X))
  let ψ := forestDist (σ.restrict S hS).clusters (σ.restrict S hS).length s
  set c := sampledForest s (A.subtype (· ∈ S))
  have hmaps : ∀ i ∈ T, P i → τ i ∈ T' :=
    fun B hB hBS => marg_subtype_mem_childClusters hH hA hB hBS (hbot B hB)
  have hinj : ∀ i ∈ T, ∀ j ∈ T, P i → P j → τ i = τ j → i = j :=
    fun B₁ hB₁ B₂ hB₂ hB₁S _ h => by_contra fun hne => by
      dsimp only [τ] at h
      obtain ⟨x, hx⟩ := subtype_nonempty_iff.2 hB₁S
      exact Finset.disjoint_left.1 (hH.disjoint_of_mem_childClusters hB₁ hB₂ hne)
        (mem_subtype.1 hx) (mem_subtype.1 (h ▸ hx))
  have hsurj : ∀ i' ∈ T', ∃ i ∈ T, P i ∧ τ i = i' := fun D hD => by
    obtain ⟨hDH, hDA, -⟩ := mem_childClusters.1 hD
    obtain ⟨x, hx⟩ := hH'.2.2.1 D hDH
    obtain ⟨y, hyA, hyD⟩ := exists_of_ssubset hDA
    have hxA : (x : X) ∈ A := mem_subtype.1 (hDA.subset hx)
    obtain ⟨B, hB, hxB⟩ := hH.exists_mem_childClusters
      (one_lt_card.2 ⟨x, hxA, y, mem_subtype.1 hyA, fun h => hyD (Subtype.ext h ▸ hx)⟩) hxA
    have hBS : (B ∩ S).Nonempty := ⟨x, mem_inter.2 ⟨hxB, x.2⟩⟩
    exact ⟨B, hB, hBS, by_contra fun hne => Finset.disjoint_left.1
      (hH'.disjoint_of_mem_childClusters (hmaps B hB hBS) hD hne) (mem_subtype.2 hxB) hx⟩
  have h0 : ∀ i ∈ T, ¬ P i → ∀ G, φ i G = if G = ∅ then 1 else 0 :=
    fun B hB hBS G => marg_forestDist_eq_empty hH σ.length (mem_childClusters.1 hB).1
      (fun l hl => hBS ⟨s l, mem_inter.2 ⟨hl, (s l).2⟩⟩) G
  have h1 : ∀ i ∈ T, P i → φ i = ψ (τ i) := fun B hB hBS => by
    funext G
    have hBu : B.subtype (· ∈ S) ≠ univ :=
      ne_of_lt (lt_of_lt_of_le (mem_childClusters.1 (hmaps B hB hBS)).2.1 (subset_univ _))
    have hlen : (σ.restrict S hS).length (B.subtype (· ∈ S)) =
        ∑ A' ∈ σ.clusters with A' ⊆ B ∧ A'.subtype (· ∈ S) = B.subtype (· ∈ S), σ.length A' := by
      show σ.restrictLength S _ = _
      unfold SpeciesTree.restrictLength
      obtain ⟨hBH, hBA, hBmax⟩ := mem_childClusters.1 hB
      refine sum_congr (filter_congr fun A' hA'H => and_congr_left fun htr => ?_) fun _ _ => rfl
      refine ⟨fun _ => ?_, fun hA'B h => not_subset_of_ssubset hBA (h ▸ subset_univ A |>.trans hA'B)⟩
      obtain ⟨x, hx⟩ := subtype_nonempty_iff.2 hBS
      have hxB : (x : X) ∈ B := mem_subtype.1 hx
      have hxA' : (x : X) ∈ A' := mem_subtype.1 (htr.symm ▸ hx)
      rcases hH.subset_or_subset_of_mem hA'H hBH hxA' hxB with h | hBA'
      · exact h
      · refine hBA'.eq_or_ssubset.elim (·.symm.subset) fun hBA' => absurd ?_ (hbot B hB)
        have hAA' : A ⊆ A' := (hH.subset_or_subset_of_mem hA'H hA hxA' (hBA.subset hxB)).elim
          (fun h => (h.eq_or_ssubset.resolve_right (hBmax A' hA'H hBA')).symm.subset) id
        exact subset_antisymm (subtype_mono hBA.subset) (htr ▸ subtype_mono hAA')
    dsimp only [φ, ψ, τ]
    rw [ih B hB hBS G, forestDist_eq_sum_entering]
    unfold populationKernel
    rw [ite_eq_right hBu, hlen]
  choose j hjT hjP hjτ using hsurj
  have hji : ∀ (i : T) (hP : P i), (⟨j (τ i) (hmaps i i.2 hP), hjT _ _⟩ : T) = i :=
    fun i hP => Subtype.ext (hinj _ (hjT _ _) i i.2 (hjP _ _) hP (hjτ _ _))
  have hij : ∀ i' : T', (⟨τ (j i'.1 i'.2), hmaps _ (hjT _ _) (hjP _ _)⟩ : T') = i' :=
    fun i' => Subtype.ext (hjτ _ _)
  rw [show (∑ f : T → Finset (Finset L), if univ.sup f ∪ c = F then ∏ i : T, φ i (f i) else 0) =
      ∑ f ∈ (univ : Finset (T → Finset (Finset L))).filter (fun f => ∀ i : T, ¬ P i → f i = ∅),
        if univ.sup f ∪ c = F then ∏ i : T, φ i (f i) else 0 from by
    refine (sum_subset (filter_subset _ _) fun f _ hf => ?_).symm
    simp only [mem_filter, mem_univ, true_and, not_forall] at hf
    obtain ⟨i, hPi, hfi⟩ := hf
    rw [prod_eq_zero (mem_univ i) (by rw [h0 i i.2 hPi, ite_eq_right hfi]), ite_self]]
  refine sum_nbij' (fun f i' => f ⟨j i'.1 i'.2, hjT _ _⟩)
    (fun g i => if h : P i then g ⟨τ i, hmaps i i.2 h⟩ else ∅)
    (fun _ _ => mem_univ _) (fun g _ => ?_) (fun f hf => ?_) (fun g _ => ?_) (fun f hf => ?_)
  · simp only [mem_filter, mem_univ, true_and]; intro i hi; rw [dite_eq_right hi]
  · simp only [mem_filter, mem_univ, true_and] at hf
    funext i; dsimp only
    by_cases hi : P i
    · rw [dite_eq_left hi, hji i hi]
    · rw [dite_eq_right hi, hf i hi]
  · funext i'; dsimp only; rw [dite_eq_left (hjP _ _), hij i']
  · simp only [mem_filter, mem_univ, true_and] at hf
    have hsup : univ.sup f = univ.sup fun i' : T' => f ⟨j i'.1 i'.2, hjT _ _⟩ := by
      refine le_antisymm (Finset.sup_le fun i _ => ?_) (Finset.sup_le fun i' _ => ?_)
      · by_cases hi : P i
        · rw [show f i = (fun i' : T' => f ⟨j i'.1 i'.2, hjT _ _⟩) ⟨τ i, hmaps i i.2 hi⟩ by
            dsimp only; rw [hji i hi]]
          exact le_sup (f := fun i' : T' => f ⟨j i'.1 i'.2, hjT _ _⟩) (mem_univ _)
        · rw [hf i hi]; exact bot_le
      · exact le_sup (f := f) (mem_univ _)
    have hprod : ∏ i : T, φ i (f i) = ∏ i' : T', ψ i' (f ⟨j i'.1 i'.2, hjT _ _⟩) := by
      rw [← prod_filter_of_ne (p := fun i : T => P i) fun i _ hne => ?_]
      · refine prod_bij' (fun i hi => ⟨τ i, hmaps i i.2 (mem_filter.1 hi).2⟩)
          (fun i' _ => ⟨j i'.1 i'.2, hjT _ _⟩) (fun _ _ => mem_univ _)
          (fun i' _ => mem_filter.2 ⟨mem_univ _, hjP _ _⟩)
          (fun i hi => hji i (mem_filter.1 hi).2) (fun i' _ => hij i')
          (fun i hi => by dsimp only; rw [h1 i i.2 (mem_filter.1 hi).2, hji i (mem_filter.1 hi).2])
      · by_contra hi
        exact hne (by rw [h0 i i.2 hi, hf i hi, ite_eq_left rfl])
    dsimp only; rw [hsup, hprod]

private theorem marg_prune (σ : SpeciesTree X) {S : Finset X} (hS : S.Nonempty) (s : L → S)
    {A : Finset X} (hA : A ∈ σ.clusters) (hAS : (A ∩ S).Nonempty)
    (G : Finset (Finset L)) :
    ∑ F, enteringDist σ.clusters σ.length (fun l => (s l : X)) A F *
        kingmanTransition (σ.length A) F G =
      ∑ F, enteringDist (σ.restrict S hS).clusters (σ.restrict S hS).length s
          (A.subtype (· ∈ S)) F *
        kingmanTransition (∑ A' ∈ σ.clusters with A' ⊆ A ∧
          A'.subtype (· ∈ S) = A.subtype (· ∈ S), σ.length A') F G := by
  have hH := σ.isHierarchy
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  have hf : ∀ B ∈ childClusters σ.clusters A, (B ∩ S).Nonempty → ∀ G,
      forestDist σ.clusters σ.length (fun l => (s l : X)) B G =
        ∑ F, enteringDist (σ.restrict S hS).clusters (σ.restrict S hS).length s
            (B.subtype (· ∈ S)) F *
          kingmanTransition (∑ A' ∈ σ.clusters with A' ⊆ B ∧
            A'.subtype (· ∈ S) = B.subtype (· ∈ S), σ.length A') F G := fun B hB hBS G => by
    obtain ⟨hBH, hBA, -⟩ := mem_childClusters.1 hB
    rw [forestDist_eq_sum_entering]
    unfold populationKernel
    rw [ite_eq_right (ne_of_lt (lt_of_lt_of_le hBA (subset_univ A))), ih B hBA hBH hBS G]
  by_cases hc : ∃ B₀ ∈ childClusters σ.clusters A, B₀.subtype (· ∈ S) = A.subtype (· ∈ S)
  · obtain ⟨B₀, hB₀, htr⟩ := hc
    obtain ⟨hB₀H, hB₀A, -⟩ := mem_childClusters.1 hB₀
    have hB₀S : (B₀ ∩ S).Nonempty :=
      subtype_nonempty_iff.1 (htr ▸ subtype_nonempty_iff.2 hAS)
    have hAB₀ : A ∉ σ.clusters.filter
        (fun A' => A' ⊆ B₀ ∧ A'.subtype (· ∈ S) = B₀.subtype (· ∈ S)) :=
      fun h => not_subset_of_ssubset hB₀A (mem_filter.1 h).2.1
    have hchain : σ.clusters.filter (fun A' => A' ⊆ A ∧ A'.subtype (· ∈ S) = A.subtype (· ∈ S)) =
        insert A (σ.clusters.filter
          (fun A' => A' ⊆ B₀ ∧ A'.subtype (· ∈ S) = B₀.subtype (· ∈ S))) := by
      ext A'; simp only [mem_insert, mem_filter]
      constructor
      · rintro ⟨hA'H, hA'A, htr'⟩
        rcases hA'A.eq_or_ssubset with h | hA'A
        · exact Or.inl h
        · obtain ⟨B, hB, hA'B⟩ := hH.exists_mem_childClusters_superset hA'H hA'A
          obtain ⟨x, hx⟩ := subtype_nonempty_iff.2 hAS
          have hBB₀ : B = B₀ := by_contra fun hne =>
            Finset.disjoint_left.1 (hH.disjoint_of_mem_childClusters hB hB₀ hne)
              (hA'B (mem_subtype.1 (htr'.symm ▸ hx))) (mem_subtype.1 (htr.symm ▸ hx))
          exact Or.inr ⟨hA'H, hBB₀ ▸ hA'B, htr'.trans htr.symm⟩
      · rintro (rfl | ⟨hA'H, hA'B₀, htr'⟩)
        · exact ⟨hA, subset_rfl, rfl⟩
        · exact ⟨hA'H, hA'B₀.trans hB₀A.subset, htr'.trans htr⟩
    rw [hchain, sum_insert hAB₀]
    calc ∑ F, enteringDist σ.clusters σ.length (fun l => (s l : X)) A F *
          kingmanTransition (σ.length A) F G
        = ∑ F, (∑ F₀, enteringDist (σ.restrict S hS).clusters (σ.restrict S hS).length s
            (B₀.subtype (· ∈ S)) F₀ * kingmanTransition (∑ A' ∈ σ.clusters with A' ⊆ B₀ ∧
              A'.subtype (· ∈ S) = B₀.subtype (· ∈ S), σ.length A') F₀ F) *
            kingmanTransition (σ.length A) F G := sum_congr rfl fun F _ => by
          rw [marg_enteringDist_chain hH σ.length (fun l => (s l).2) hB₀ htr, hf B₀ hB₀ hB₀S F]
      _ = _ := by
          simp_rw [sum_mul]; rw [sum_comm]
          refine sum_congr rfl fun F₀ _ => ?_
          rw [htr, add_comm, kingmanTransition_add, Matrix.mul_apply, mul_sum]
          exact sum_congr rfl fun F _ => by ring
  · push Not at hc
    have hbot : σ.clusters.filter (fun A' => A' ⊆ A ∧ A'.subtype (· ∈ S) = A.subtype (· ∈ S)) =
        {A} := by
      ext A'; simp only [mem_filter, mem_singleton]
      refine ⟨fun ⟨hA'H, hA'A, htr'⟩ => by_contra fun hne => ?_,
        fun h => h.symm ▸ ⟨hA, subset_rfl, rfl⟩⟩
      obtain ⟨B, hB, hA'B⟩ := hH.exists_mem_childClusters_superset hA'H (hA'A.ssubset_of_ne hne)
      exact hc B hB (subset_antisymm (subtype_mono (mem_childClusters.1 hB).2.1.subset)
        (htr' ▸ subtype_mono hA'B))
    rw [hbot, sum_singleton]
    exact sum_congr rfl fun F _ => by rw [marg_enteringDist_restrict σ hS s hA hc hf F]

private theorem marg_rootedDist_eq_sum_transition (σ : SpeciesTree X) (s : L → X) (t : ℝ)
    (G : Finset (Finset L)) :
    σ.rootedDist s G =
      ∑ H', (∑ F, enteringDist σ.clusters σ.length s univ F * kingmanTransition t F H') *
        kingmanAbsorption H' G := by
  unfold SpeciesTree.rootedDist
  rw [forestDist_eq_sum_entering]; unfold populationKernel; rw [ite_eq_left rfl]
  simp_rw [sum_mul]; rw [sum_comm]
  refine sum_congr rfl fun F _ => ?_
  by_cases h0 : enteringDist σ.clusters σ.length s univ F = 0
  · simp [h0]
  · simp_rw [mul_assoc, ← mul_sum]
    rw [kingmanTransition_mul_kingmanAbsorption (enteringDist_support σ.isHierarchy _ s h0).1]

theorem SpeciesTree.rootedDist_restrict (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty)
    (s : L → S) (G : Finset (Finset L)) :
    (σ.restrict S hS).rootedDist s G = σ.rootedDist (fun l => (s l : X)) G := by
  rw [marg_rootedDist_eq_sum_transition (σ.restrict S hS) s
      (∑ A' ∈ σ.clusters with A' ⊆ univ ∧
        A'.subtype (· ∈ S) = (univ : Finset X).subtype (· ∈ S), σ.length A'),
    marg_rootedDist_eq_sum_transition σ _ (σ.length univ)]
  refine sum_congr rfl fun H' _ => ?_
  rw [marg_prune σ hS s σ.univ_mem (by simpa using hS) H', subtype_univ]

/-! ### Unrooting -/

def restrictUnrooted (e : L' ↪ L) (T : Finset (Finset L)) : Finset (Finset L') :=
  (T.filter fun A => (∃ l, e l ∈ A) ∧ ∃ l, e l ∉ A).image (tr e)

private theorem marg_tr_compl (e : L' ↪ L) (A : Finset L) : (tr e A)ᶜ = tr e Aᶜ := by
  ext l; simp [tr]

omit [Fintype L] [DecidableEq L'] in
private theorem marg_tr_ne_univ (e : L' ↪ L) {A : Finset L} :
    tr e A ≠ univ ↔ ∃ l, e l ∉ A := by
  simp [tr, ne_eq, eq_univ_iff_forall]

private theorem marg_unroot_restrictForest (e : L' ↪ L) (G : Finset (Finset L)) :
    unroot (restrictForest e G) = restrictUnrooted e (unroot G) := by
  ext D
  simp only [absorb_mem_unroot, restrictUnrooted, mem_image, mem_filter]
  constructor
  · rintro (⟨hD, hDu⟩ | ⟨hD, hDu⟩)
    · obtain ⟨A, hA, hAm, rfl⟩ := (marg_mem_restrictForest e).1 hD
      have hout := (marg_tr_ne_univ e).1 hDu
      exact ⟨A, ⟨Or.inl ⟨hA, fun h => let ⟨l, hl⟩ := hout; hl (h ▸ mem_univ _)⟩, hAm, hout⟩, rfl⟩
    · obtain ⟨A, hA, hAm, hAD⟩ := (marg_mem_restrictForest e).1 hD
      have hout := (marg_tr_ne_univ e).1 (hAD ▸ hDu)
      have hAu : A ≠ univ := fun h => let ⟨l, hl⟩ := hout; hl (h ▸ mem_univ _)
      refine ⟨Aᶜ, ⟨Or.inr ⟨by rwa [compl_compl], by rwa [compl_compl]⟩,
        by simpa using hout, by simpa using hAm⟩, by rw [← marg_tr_compl, hAD, compl_compl]⟩
  · rintro ⟨A, ⟨⟨hA, -⟩ | ⟨hA, -⟩, hAm, hout⟩, rfl⟩
    · exact Or.inl ⟨marg_tr_mem_restrictForest e hA hAm, (marg_tr_ne_univ e).2 hout⟩
    · right
      rw [marg_tr_compl]
      exact ⟨marg_tr_mem_restrictForest e hA (by simpa using hout),
        (marg_tr_ne_univ e).2 (by simpa using hAm)⟩

theorem SpeciesTree.unrootedDist_comp_embedding (σ : SpeciesTree X) (s : L → X) (e : L' ↪ L)
    (T' : Finset (Finset L')) :
    σ.unrootedDist (s ∘ e) T' =
      ∑ T, if restrictUnrooted e T = T' then σ.unrootedDist s T else 0 := by
  unfold SpeciesTree.unrootedDist
  simp_rw [σ.rootedDist_comp_embedding s e]
  rw [marg_sum_ite_comp (restrictForest e) unroot (σ.rootedDist s) T',
    marg_sum_ite_comp unroot (restrictUnrooted e) (σ.rootedDist s) T']
  simp_rw [marg_unroot_restrictForest]

/-! ### Extending species trees for multiple samples -/

def extendClusters (H : Finset (Finset X)) (s : L → X) : Finset (Finset L) :=
  H.image (pre s) ∪ univ.image fun l => {l}

omit [Fintype X] in
private lemma multi_mem_extendClusters {H : Finset (Finset X)} (s : L → X) {A : Finset X}
    (hA : A ∈ H) : pre s A ∈ extendClusters H s :=
  mem_union_left _ (mem_image_of_mem _ hA)

omit [DecidableEq L] in
private lemma multi_pre_univ (s : L → X) : pre s (univ : Finset X) = univ :=
  filter_true_of_mem fun _ _ => mem_univ _

omit [Fintype X] [DecidableEq L] in
private lemma multi_pre_subset_pre {s : L → X} (hs : Function.Surjective s) {A B : Finset X} :
    pre s A ⊆ pre s B ↔ A ⊆ B := by
  refine ⟨fun h x hx => ?_, marg_tr_mono s⟩
  obtain ⟨l, rfl⟩ := hs x
  exact (mem_filter.1 (h (mem_filter.2 ⟨mem_univ l, hx⟩))).2

omit [Fintype X] [DecidableEq L] in
private lemma multi_pre_inj {s : L → X} (hs : Function.Surjective s) {A B : Finset X} :
    pre s A = pre s B ↔ A = B :=
  ⟨fun h => subset_antisymm ((multi_pre_subset_pre hs).1 h.le) ((multi_pre_subset_pre hs).1 h.ge),
    fun h => h ▸ rfl⟩

omit [Fintype X] [DecidableEq L] in
private lemma multi_pre_ssubset_pre {s : L → X} (hs : Function.Surjective s) {A B : Finset X} :
    pre s A ⊂ pre s B ↔ A ⊂ B := by
  rw [ssubset_iff_subset_ne, ssubset_iff_subset_ne, multi_pre_subset_pre hs, Ne, Ne,
    multi_pre_inj hs]

omit [DecidableEq L] in
private lemma multi_pre_ne_univ {s : L → X} (hs : Function.Surjective s) {A : Finset X}
    (hA : A ≠ univ) : pre s A ≠ univ :=
  fun h => hA ((multi_pre_inj hs).1 (h.trans (multi_pre_univ s).symm))

omit [Fintype X] [DecidableEq L] in
private lemma multi_pre_nonempty {s : L → X} (hs : Function.Surjective s) {A : Finset X}
    (hA : A.Nonempty) : (pre s A).Nonempty := by
  obtain ⟨x, hx⟩ := hA; obtain ⟨l, rfl⟩ := hs x
  exact ⟨l, mem_filter.2 ⟨mem_univ l, hx⟩⟩

omit [Fintype X] [DecidableEq L] in
private lemma multi_card_le_card_pre {s : L → X} (hs : Function.Surjective s) (A : Finset X) :
    #A ≤ #(pre s A) := by
  refine (card_le_card (t := (pre s A).image s) fun x hx => ?_).trans card_image_le
  obtain ⟨l, rfl⟩ := hs x
  exact mem_image_of_mem s (mem_filter.2 ⟨mem_univ l, hx⟩)

omit [Fintype X] in
private lemma multi_sampledForest_pre (s : L → X) (A : Finset X) :
    sampledForest s A = sampledForest id (pre s A) := by
  unfold sampledForest; congr 1; ext l; simp [pre]

noncomputable def SpeciesTree.extendLength (σ : SpeciesTree X) (s : L → X) (B : Finset L) : ℝ :=
  if h : ∃ A ∈ σ.clusters, pre s A = B ∧ 2 ≤ #B then
    σ.length h.choose else 1

noncomputable def SpeciesTree.extend (σ : SpeciesTree X) (s : L → X)
    (hs : Function.Surjective s) : SpeciesTree L where
  clusters := extendClusters σ.clusters s
  univ_mem := by rw [← multi_pre_univ s]; exact multi_mem_extendClusters s σ.univ_mem
  singleton_mem l := mem_union_right _ (mem_image_of_mem _ (mem_univ l))
  nonempty_of_mem B hB := by
    rcases mem_union.1 hB with hB | hB
    · obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
      exact multi_pre_nonempty hs (σ.nonempty_of_mem A hA)
    · obtain ⟨l, -, rfl⟩ := mem_image.1 hB; exact singleton_nonempty l
  laminar B hB C hC := by
    rcases mem_union.1 hB with hB | hB
    · obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
      rcases mem_union.1 hC with hC | hC
      · obtain ⟨A', hA', rfl⟩ := mem_image.1 hC
        rcases σ.laminar A hA A' hA' with h | h | h
        · exact Or.inl (marg_tr_mono s h)
        · exact Or.inr (Or.inl (marg_tr_mono s h))
        · exact Or.inr (Or.inr (marg_tr_disjoint s h))
      · obtain ⟨l, -, rfl⟩ := mem_image.1 hC
        rcases msc_singleton_laminar l (pre s A) with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h.symm)
    · obtain ⟨l, -, rfl⟩ := mem_image.1 hB
      exact msc_singleton_laminar l C
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
    populationKernel (L := L) σ.length A =
      populationKernel (σ.extendLength s) (pre s A) := by
  unfold populationKernel
  by_cases hAu : A = univ
  · subst hAu; rw [ite_eq_left rfl, ite_eq_left (multi_pre_univ s)]
  · rw [ite_eq_right hAu, ite_eq_right (multi_pre_ne_univ hs hAu),
      multi_extendLength_pre σ hs hA h2]

private lemma multi_childClusters_pre (σ : SpeciesTree X) {s : L → X}
    (hs : Function.Surjective s) {A : Finset X} (h2 : 2 ≤ #A) :
    childClusters (extendClusters σ.clusters s) (pre s A) =
      (childClusters σ.clusters A).image (pre s) := by
  ext C; rw [mem_image]
  constructor
  · intro hC
    obtain ⟨hCE, hCA, hmax⟩ := mem_childClusters.1 hC
    rcases mem_union.1 hCE with hCE | hCE
    · obtain ⟨D, hD, rfl⟩ := mem_image.1 hCE
      refine ⟨D, mem_childClusters.2 ⟨hD, (multi_pre_ssubset_pre hs).1 hCA,
        fun D' hD' hDD' hD'A => hmax _ (multi_mem_extendClusters s hD')
          ((multi_pre_ssubset_pre hs).2 hDD') ((multi_pre_ssubset_pre hs).2 hD'A)⟩, rfl⟩
    · obtain ⟨l, -, rfl⟩ := mem_image.1 hCE
      have hl : s l ∈ A := (mem_filter.1 (hCA.subset (mem_singleton_self l))).2
      obtain ⟨B, hB, hlB⟩ := σ.isHierarchy.exists_mem_childClusters h2 hl
      refine ⟨B, hB, ?_⟩
      rcases (singleton_subset_iff.2 (mem_filter.2 ⟨mem_univ l, hlB⟩) :
        {l} ⊆ pre s B).eq_or_ssubset with h | h
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
      Equiv.ofBijective (fun B => ⟨pre s B, hch ▸ mem_image_of_mem _ B.2⟩)
        ⟨fun B B' h => Subtype.ext ((multi_pre_inj hs).1 (congrArg Subtype.val h)), fun C => by
          obtain ⟨B, hB, hBC⟩ := mem_image.1 (by rw [← hch]; exact C.2)
          exact ⟨⟨B, hB⟩, Subtype.ext hBC⟩⟩
    rw [forestDist.eq_1 σ.clusters σ.length, forestDist.eq_1 (extendClusters σ.clusters s),
      ← (e.arrowCongr (Equiv.refl _)).sum_comp]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hΦ : (e.arrowCongr (Equiv.refl _)) g = fun C => g (e.symm C) := rfl
    rw [hΦ]
    congr 1
    · refine Fintype.prod_equiv e _ _ fun B => ?_
      dsimp only
      rw [e.symm_apply_apply]
      exact ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1 _
    · rw [multi_populationKernel_pre σ hs hA hpre2, multi_sampledForest_pre s A]
      congr 2
      refine le_antisymm (Finset.sup_le fun B _ => ?_) (Finset.sup_le fun C _ => ?_)
      · simpa using Finset.le_sup (f := fun C => g (e.symm C)) (mem_univ (e B))
      · exact Finset.le_sup (mem_univ _)
  · have hAx : A = {x} :=
      eq_singleton_iff_unique_mem.2 ⟨hx, fun y hy => card_le_one.1 hA1 y hy x hx⟩
    subst hAx
    have hP2 : #(pre s {x}) ≤ 2 := by simpa only [pre, mem_singleton] using h2 x
    have hchB : ∀ B : childClusters (extendClusters σ.clusters s) (pre s {x}), ∀ F,
        forestDist (extendClusters σ.clusters s) (σ.extendLength s) id B F =
          if F = sampledForest id (B : Finset L) then 1 else 0 := fun B F => by
      have hB1 : #(B : Finset L) ≤ 1 :=
        Nat.le_of_lt_succ ((card_lt_card (mem_childClusters.1 B.2).2.1).trans_le hP2)
      have hemp : childClusters (extendClusters σ.clusters s) (B : Finset L) = ∅ :=
        filter_eq_empty_iff.2 fun C hC hCB =>
          absurd (card_pos.2 (hE.2.2.1 C hC)) (by have := card_lt_card hCB.1; omega)
      rw [forestDist_of_childClusters_eq_empty hemp,
        populationKernel_sampledForest_of_card_le_one (σ.extendLength s)
          (by dsimp only [id]; rw [filter_mem_eq_inter, univ_inter]; exact hB1)]
    rw [forestDist_of_childClusters_eq_empty (σ.isHierarchy.childClusters_singleton x),
      forestDist.eq_1 (extendClusters σ.clusters s),
      Finset.sum_eq_single (fun B : childClusters (extendClusters σ.clusters s) (pre s {x}) =>
        sampledForest id (B : Finset L))]
    · simp only [hchB, ite_true, prod_const_one, one_mul]
      have hsup : (univ.sup fun B : childClusters (extendClusters σ.clusters s) (pre s {x}) =>
          sampledForest id (B : Finset L)) ∪ sampledForest id (pre s {x}) =
            sampledForest s {x} := by
        rw [multi_sampledForest_pre s {x}]
        refine union_eq_right.2 fun C hC => ?_
        obtain ⟨B, -, hCB⟩ := Finset.mem_sup.1 hC
        obtain ⟨l, hl, rfl⟩ := mem_sampledForest.1 hCB
        exact mem_sampledForest.2 ⟨l, (mem_childClusters.1 B.2).2.1.subset hl, rfl⟩
      rw [hsup]
      by_cases hge2 : 2 ≤ #(pre s {x})
      · rw [multi_populationKernel_pre σ hs hA hge2]
      · have hle1 : #(pre s {x}) ≤ 1 := by omega
        rw [populationKernel_sampledForest_of_card_le_one σ.length hle1,
          multi_sampledForest_pre s {x},
          populationKernel_sampledForest_of_card_le_one (σ.extendLength s)
            (by dsimp only [id]; rw [filter_mem_eq_inter, univ_inter]; exact hle1)]
    · intro f _ hf
      obtain ⟨B, hB⟩ := Function.ne_iff.1 hf
      rw [prod_eq_zero (mem_univ B) (by rw [hchB, ite_eq_right hB]), zero_mul]
    · simp

theorem SpeciesTree.rootedDist_extend (σ : SpeciesTree X) {s : L → X}
    (hs : Function.Surjective s) (h2 : ∀ x, #(univ.filter fun l => s l = x) ≤ 2)
    (G : Finset (Finset L)) :
    σ.rootedDist s G = (σ.extend s hs).rootedDist id G := by
  unfold SpeciesTree.rootedDist
  rw [multi_forestDist_extend σ hs h2 σ.univ_mem G, multi_pre_univ]; rfl

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
    rcases mem_union.1 (hcl ▸ multi_mem_extendClusters s hA) with h | h
    · obtain ⟨A', hA', hA'A⟩ := mem_image.1 h
      rwa [(multi_pre_inj hs).1 hA'A] at hA'
    · obtain ⟨l, -, hl⟩ := mem_image.1 h
      have hlA : l ∈ pre s A := hl ▸ mem_singleton_self l
      have hAsl : A = {s l} := eq_singleton_iff_unique_mem.2
        ⟨(mem_filter.1 hlA).2, fun y hy => by
          obtain ⟨l', rfl⟩ := hs y
          have : l' ∈ ({l} : Finset L) := hl ▸ mem_filter.2 ⟨mem_univ l', hy⟩
          rw [mem_singleton.1 this]⟩
      exact hAsl ▸ τ'.singleton_mem _
  have hcl' : σ.clusters = σ'.clusters :=
    subset_antisymm (fun A hA => hmem hcl A hA) (fun A hA => hmem hcl.symm A hA)
  have key : ∀ A ∈ σ.clusters, 2 ≤ #(pre s A) → A ≠ univ → σ.length A = σ'.length A := by
    intro A hA h2 hAu
    have := hlen _ (multi_mem_extendClusters s hA) h2 (multi_pre_ne_univ hs hAu)
    change σ.extendLength s _ = σ'.extendLength s _ at this
    rwa [multi_extendLength_pre σ hs hA h2, multi_extendLength_pre σ' hs (hcl' ▸ hA) h2] at this
  refine ⟨⟨hcl', fun A hA hA2 hAu => key A hA (hA2.trans (multi_card_le_card_pre hs A)) hAu⟩,
    fun x hx => key {x} (σ.singleton_mem x) (by simpa only [pre, mem_singleton] using hx)
      fun hxu => ?_⟩
  have := congrArg card hxu; rw [card_singleton, card_univ] at this; omega

end ADR11
