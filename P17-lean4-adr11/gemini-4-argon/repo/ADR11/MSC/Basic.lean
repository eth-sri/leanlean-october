module

public import ADR11.Coalescent.Factorization

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] {L : Type*} [Fintype L] [DecidableEq L]

def IsHierarchy (H : Finset (Finset X)) : Prop :=
  univ ∈ H ∧ (∀ x : X, {x} ∈ H) ∧ (∀ A ∈ H, A.Nonempty) ∧
    ∀ A ∈ H, ∀ B ∈ H, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

theorem SpeciesTree.isHierarchy (σ : SpeciesTree X) : IsHierarchy σ.clusters :=
  ⟨σ.univ_mem, σ.singleton_mem, σ.nonempty_of_mem, σ.laminar⟩

noncomputable def enteringDist (H : Finset (Finset X)) (len : Finset X → ℝ) (s : L → X)
    (A : Finset X) (F : Finset (Finset L)) : ℝ :=
  ∑ f : childClusters H A → Finset (Finset L),
    if univ.sup f ∪ sampledForest s A = F then ∏ B : childClusters H A, forestDist H len s B (f B)
    else 0

theorem forestDist_eq_sum_entering (H : Finset (Finset X)) (len : Finset X → ℝ) (s : L → X)
    (A : Finset X) (G : Finset (Finset L)) :
    forestDist H len s A G = ∑ F, enteringDist H len s A F * populationKernel len A F G := by
  rw [forestDist]
  unfold enteringDist
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]; simp

theorem forestDist_of_childClusters_eq_empty {H : Finset (Finset X)} {len : Finset X → ℝ}
    {s : L → X} {A : Finset X} (h : childClusters H A = ∅) (G : Finset (Finset L)) :
    forestDist H len s A G = populationKernel len A (sampledForest s A) G := by
  rw [forestDist]
  have : IsEmpty (childClusters H A) := by rw [h]; infer_instance
  rw [Fintype.sum_unique]; simp

theorem mem_childClusters {H : Finset (Finset X)} {A B : Finset X} :
    B ∈ childClusters H A ↔ B ∈ H ∧ B ⊂ A ∧ ∀ C ∈ H, B ⊂ C → ¬ C ⊂ A :=
  mem_filter

theorem IsHierarchy.childClusters_singleton {H : Finset (Finset X)} (hH : IsHierarchy H) (x : X) :
    childClusters H {x} = ∅ := by
  unfold childClusters
  rw [Finset.filter_eq_empty_iff]
  rintro B hB ⟨hBx, -⟩
  rw [Finset.ssubset_singleton_iff] at hBx
  exact Finset.not_nonempty_empty (hBx ▸ hH.2.2.1 _ hB)

theorem IsHierarchy.disjoint_of_mem_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A B C : Finset X} (hB : B ∈ childClusters H A) (hC : C ∈ childClusters H A) (hBC : B ≠ C) :
    Disjoint B C := by
  rw [mem_childClusters] at hB hC
  rcases hH.2.2.2 B hB.1 C hC.1 with h | h | h
  · exact absurd hC.2.1 (hB.2.2 C hC.1 (lt_of_le_of_ne h hBC))
  · exact absurd hB.2.1 (hC.2.2 B hB.1 (lt_of_le_of_ne h hBC.symm))
  · exact h

omit [Fintype X] in
theorem mem_sampledForest {s : L → X} {A : Finset X} {C : Finset L} :
    C ∈ sampledForest s A ↔ ∃ l, s l ∈ A ∧ {l} = C := by
  simp [sampledForest]

omit [Fintype L] in
theorem msc_singleton_laminar (l : L) (D : Finset L) :
    {l} ⊆ D ∨ D ⊆ {l} ∨ Disjoint {l} D :=
  if h : l ∈ D then Or.inl (singleton_subset_iff.2 h)
  else Or.inr (Or.inr (disjoint_singleton_left.2 h))

theorem IsHierarchy.isForest_entering {H : Finset (Finset X)} (hH : IsHierarchy H) {s : L → X}
    {A : Finset X} (f : childClusters H A → Finset (Finset L))
    (hf : ∀ B, IsForest (f B) ∧ lineages (f B) = univ.filter (fun l => s l ∈ (B : Finset X))) :
    IsForest (univ.sup f ∪ sampledForest s A) ∧
      sampledForest s A ⊆ univ.sup f ∪ sampledForest s A ∧
      lineages (univ.sup f ∪ sampledForest s A) = univ.filter (fun l => s l ∈ A) := by
  have hsub : ∀ (B : childClusters H A) (C : Finset L), C ∈ f B → ∀ l ∈ C,
      s l ∈ (B : Finset X) := fun B C hC l hl => by
    have : l ∈ lineages (f B) := mem_lineages.2 ⟨C, hC, hl⟩
    rw [(hf B).2, mem_filter] at this; exact this.2
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
        · subst hBB'; exact (hf B).1.2 C hCB D hDB'
        · refine Or.inr (Or.inr (Finset.disjoint_left.2 fun l hlC hlD => ?_))
          exact Finset.disjoint_left.1
            (hH.disjoint_of_mem_childClusters B.2 B'.2 fun h => hBB' (Subtype.ext h))
            (hsub B C hCB l hlC) (hsub B' D hDB' l hlD)
      · obtain ⟨l, -, rfl⟩ := mem_sampledForest.1 hC'
        exact msc_singleton_laminar l D
    · obtain ⟨l, -, rfl⟩ := mem_sampledForest.1 hD'
      rcases msc_singleton_laminar l C with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h.symm)
  · ext l
    rw [mem_lineages, mem_filter]
    constructor
    · rintro ⟨C, hC, hlC⟩
      refine ⟨mem_univ _, ?_⟩
      rcases mem_union.1 hC with hC | hC
      · obtain ⟨B, -, hCB⟩ := Finset.mem_sup.1 hC
        exact (mem_childClusters.1 B.2).2.1.1 (hsub B C hCB l hlC)
      · obtain ⟨l', hl', rfl⟩ := mem_sampledForest.1 hC
        exact mem_singleton.1 hlC ▸ hl'
    · rintro ⟨-, h⟩
      exact ⟨{l}, mem_union_right _ (mem_sampledForest.2 ⟨l, h, rfl⟩), mem_singleton_self l⟩

theorem forestDist_support {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) {A : Finset X} (hA : A ∈ H) {G : Finset (Finset L)}
    (hG : forestDist H len s A G ≠ 0) :
    IsForest G ∧ sampledForest s A ⊆ G ∧ lineages G = univ.filter (fun l => s l ∈ A) := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist] at hG
  obtain ⟨f, -, hf⟩ := Finset.exists_ne_zero_of_sum_ne_zero hG
  have hprod := left_ne_zero_of_mul hf
  obtain ⟨hF, hSF, hLF⟩ := hH.isForest_entering f fun B =>
    let ⟨h1, _, h3⟩ := ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1
      (Finset.prod_ne_zero_iff.1 hprod B (mem_univ _))
    ⟨h1, h3⟩
  have hK := right_ne_zero_of_mul hf
  unfold populationKernel at hK
  obtain ⟨hG1, hG2, hG3⟩ : IsForest G ∧ _ ⊆ G ∧ lineages G = _ := by
    split_ifs at hK with hAu
    · rw [kingmanAbsorption_apply hF] at hK
      split_ifs at hK with h0 h1 h2
      · subst h1; exact ⟨hF, subset_rfl, rfl⟩
      · exact absurd rfl hK
      · obtain ⟨h1, h2, h3, -⟩ := jumpMatrix_pow_support hF hK
        exact ⟨h1, h2, h3⟩
      · exact absurd rfl hK
    · rw [kingmanTransition_apply hF] at hK
      obtain ⟨h1, h2, h3, -⟩ := jumpMatrix_pow_support hF (right_ne_zero_of_mul hK)
      exact ⟨h1, h2, h3⟩
  exact ⟨hG1, hSF.trans hG2, hG3.trans hLF⟩

private lemma msc_isForest_entering_of_prod {H : Finset (Finset X)} (hH : IsHierarchy H)
    {len : Finset X → ℝ} {s : L → X} {A : Finset X}
    {f : childClusters H A → Finset (Finset L)}
    (hprod : ∏ B : childClusters H A, forestDist H len s B (f B) ≠ 0) :
    IsForest (univ.sup f ∪ sampledForest s A) ∧
      sampledForest s A ⊆ univ.sup f ∪ sampledForest s A ∧
      lineages (univ.sup f ∪ sampledForest s A) = univ.filter (fun l => s l ∈ A) :=
  hH.isForest_entering f fun B =>
    let ⟨h1, _, h3⟩ := forestDist_support hH len s (mem_childClusters.1 B.2).1
      (Finset.prod_ne_zero_iff.1 hprod B (mem_univ _))
    ⟨h1, h3⟩

theorem forestDist_nonneg_of_ne_univ {H : Finset (Finset X)} (hH : IsHierarchy H)
    {len : Finset X → ℝ} (hlen : ∀ A ∈ H, A ≠ univ → 0 ≤ len A) (s : L → X) {A : Finset X}
    (hA : A ∈ H) (G : Finset (Finset L)) : 0 ≤ forestDist H len s A G := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist]
  refine Finset.sum_nonneg fun f _ => ?_
  by_cases hprod : ∏ B : childClusters H A, forestDist H len s B (f B) = 0
  · rw [hprod, zero_mul]
  · refine mul_nonneg (Finset.prod_nonneg fun B _ =>
      ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1 _) ?_
    have hF := (msc_isForest_entering_of_prod hH hprod).1
    unfold populationKernel
    split_ifs with hAu
    · exact kingmanAbsorption_nonneg hF G
    · exact kingmanTransition_nonneg (hlen A hA hAu) _ G

theorem forestDist_sum {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) {A : Finset X} (hA : A ∈ H) : ∑ G, forestDist H len s A G = 1 := by
  induction A using Finset.strongInduction with
  | H A ih =>
  have hunf : ∀ G, forestDist H len s A G = ∑ f : childClusters H A → Finset (Finset L),
      (∏ B : childClusters H A, forestDist H len s B (f B)) *
        populationKernel len A (univ.sup f ∪ sampledForest s A) G := fun G => by rw [forestDist]
  simp_rw [hunf]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hterm : ∀ f : childClusters H A → Finset (Finset L),
      (∏ B : childClusters H A, forestDist H len s B (f B)) *
        ∑ G, populationKernel len A (univ.sup f ∪ sampledForest s A) G =
      ∏ B : childClusters H A, forestDist H len s B (f B) := fun f => by
    by_cases hprod : ∏ B : childClusters H A, forestDist H len s B (f B) = 0
    · rw [hprod, zero_mul]
    · have hF := (msc_isForest_entering_of_prod hH hprod).1
      have hK : ∑ G, populationKernel len A (univ.sup f ∪ sampledForest s A) G = 1 := by
        unfold populationKernel
        split_ifs
        · exact kingmanAbsorption_sum hF
        · exact kingmanTransition_sum hF (len A)
      rw [hK, mul_one]
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun (B : childClusters H A) (F : Finset (Finset L)) =>
    forestDist H len s B F)]
  exact Finset.prod_eq_one fun B _ =>
    ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1

theorem enteringDist_support {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) {A : Finset X} {F : Finset (Finset L)} (hF : enteringDist H len s A F ≠ 0) :
    IsForest F ∧ sampledForest s A ⊆ F ∧ lineages F = univ.filter (fun l => s l ∈ A) := by
  unfold enteringDist at hF
  obtain ⟨f, -, hf⟩ := Finset.exists_ne_zero_of_sum_ne_zero hF
  split_ifs at hf with hfF
  · subst hfF; exact msc_isForest_entering_of_prod hH hf
  · exact absurd rfl hf

theorem IsHierarchy.exists_mem_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A : Finset X} (hA : 2 ≤ #A) {x : X} (hx : x ∈ A) : ∃ B ∈ childClusters H A, x ∈ B := by
  have hxA : ({x} : Finset X) ⊂ A :=
    (singleton_subset_iff.2 hx).ssubset_of_ne fun e => by subst e; simp at hA
  obtain ⟨B, hB, hmax⟩ := (H.filter fun C => x ∈ C ∧ C ⊂ A).exists_max_image card
    ⟨{x}, mem_filter.2 ⟨hH.2.1 x, mem_singleton_self x, hxA⟩⟩
  rw [mem_filter] at hB
  refine ⟨B, mem_childClusters.2 ⟨hB.1, hB.2.2, fun C hC hBC hCA => ?_⟩, hB.2.1⟩
  exact absurd (card_lt_card hBC)
    (not_lt.2 (hmax C (mem_filter.2 ⟨hC, hBC.subset hB.2.1, hCA⟩)))

theorem populationKernel_sampledForest_of_card_le_one (len : Finset X → ℝ) {s : L → X}
    {A : Finset X} (hA : #(univ.filter fun l => s l ∈ A) ≤ 1) (G : Finset (Finset L)) :
    populationKernel len A (sampledForest s A) G = if G = sampledForest s A then 1 else 0 := by
  have hF := isForest_sampledForest s A
  have hk : #(roots (sampledForest s A)) ≤ 1 :=
    (card_le_card (roots_subset _)).trans (card_image_le.trans hA)
  by_cases hAu : A = univ
  · rw [populationKernel, ite_eq_left hAu, kingmanAbsorption_apply hF]
    by_cases h0 : #(roots (sampledForest s A)) = 0
    · rw [ite_eq_left h0]
    · have h1 : #(roots (sampledForest s A)) = 1 := by omega
      rw [ite_eq_right h0, h1, Nat.sub_self, pow_zero, Matrix.one_apply]
      by_cases hG : G = sampledForest s A
      · subst hG; simp [h1]
      · simp [hG, Ne.symm hG]
  · rw [populationKernel, ite_eq_right hAu]
    exact kingmanTransition_of_card_roots_le_one hF hk _ G

theorem unrootedDist_nonneg (σ : SpeciesTree X) (s : L → X) (T : Finset (Finset L)) :
    0 ≤ σ.unrootedDist s T := by
  unfold SpeciesTree.unrootedDist SpeciesTree.rootedDist
  refine Finset.sum_nonneg fun G _ => ?_
  split_ifs
  · exact forestDist_nonneg_of_ne_univ σ.isHierarchy
      (fun A hA hAu => (σ.length_pos A hA hAu).le) s σ.univ_mem G
  · exact le_rfl

theorem unrootedDist_sum (σ : SpeciesTree X) (s : L → X) : ∑ T, σ.unrootedDist s T = 1 := by
  unfold SpeciesTree.unrootedDist SpeciesTree.rootedDist
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq, mem_univ, ite_true]
  exact forestDist_sum σ.isHierarchy σ.length s σ.univ_mem

namespace IsHierarchy

variable {H : Finset (Finset X)}

omit [DecidableEq X] in
theorem subset_or_subset_of_mem (hH : IsHierarchy H) {A B : Finset X} (hA : A ∈ H) (hB : B ∈ H)
    {x : X} (hxA : x ∈ A) (hxB : x ∈ B) : A ⊆ B ∨ B ⊆ A := by
  rcases hH.2.2.2 A hA B hB with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd hxB (disjoint_left.1 h hxA)

omit [DecidableEq X] in
theorem subset_or_subset_of_not_disjoint (hH : IsHierarchy H) {A B : Finset X} (hA : A ∈ H)
    (hB : B ∈ H) (hAB : ¬ Disjoint A B) : A ⊆ B ∨ B ⊆ A := by
  obtain ⟨x, hxA, hxB⟩ := not_disjoint_iff.1 hAB
  exact hH.subset_or_subset_of_mem hA hB hxA hxB

theorem subset_of_mem_childClusters (hH : IsHierarchy H) {A B C : Finset X}
    (hB : B ∈ childClusters H A) (hC : C ∈ H) (hCA : C ⊂ A) (hBC : ¬ Disjoint B C) : C ⊆ B := by
  rw [mem_childClusters] at hB
  rcases hH.subset_or_subset_of_not_disjoint hB.1 hC hBC with h | h
  · by_contra hCB
    exact hB.2.2 C hC (ssubset_of_subset_not_subset h hCB) hCA
  · exact h

theorem exists_mem_childClusters_superset (hH : IsHierarchy H) {A B : Finset X} (hB : B ∈ H)
    (hBA : B ⊂ A) : ∃ C ∈ childClusters H A, B ⊆ C := by
  obtain ⟨b, hb⟩ := hH.2.2.1 B hB
  obtain ⟨y, hyA, hyB⟩ := exists_of_ssubset hBA
  obtain ⟨C, hC, hbC⟩ := hH.exists_mem_childClusters
    (one_lt_card.2 ⟨b, hBA.subset hb, y, hyA, fun e => hyB (e ▸ hb)⟩) (hBA.subset hb)
  exact ⟨C, hC, hH.subset_of_mem_childClusters hC hB hBA (not_disjoint_iff.2 ⟨b, hbC, hb⟩)⟩

theorem exists_pair_of_two_le_card (hH : IsHierarchy H) {N : Finset X} (hN : 2 ≤ #N) :
    ∃ x ∈ N, ∃ y ∈ N, x ≠ y ∧ ∀ C ∈ H, x ∈ C → y ∈ C → ¬ C ⊂ N := by
  obtain ⟨x, hx⟩ : N.Nonempty := card_pos.1 (by omega)
  obtain ⟨M, hM, hxM⟩ := hH.exists_mem_childClusters hN hx
  obtain ⟨y, hyN, hyM⟩ := exists_of_ssubset (mem_childClusters.1 hM).2.1
  exact ⟨x, hx, y, hyN, fun e => hyM (e ▸ hxM), fun C hC hxC hyC hCN =>
    hyM (hH.subset_of_mem_childClusters hM hC hCN (not_disjoint_iff.2 ⟨x, hxM, hxC⟩) hyC)⟩

theorem mem_of_triples (hH : IsHierarchy H) {A : Finset X}
    (hA : A.Nonempty) (h : ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∉ A, ∃ C ∈ H, a ∈ C ∧ a' ∈ C ∧ b ∉ C) :
    A ∈ H := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨L, hL, hLmin⟩ := (H.filter (A ⊆ ·)).exists_min_image card
    ⟨univ, mem_filter.2 ⟨hH.1, subset_univ A⟩⟩
  obtain ⟨hLH, hAL⟩ := mem_filter.1 hL
  suffices hsub : L ⊆ A from Subset.antisymm hsub hAL ▸ hLH
  intro b hbL
  by_contra hbA
  obtain ⟨C₀, hC₀, haC₀, -, hbC₀⟩ := h a ha a ha b hbA
  obtain ⟨U, hU, hUmax⟩ := (H.filter fun C => a ∈ C ∧ b ∉ C).exists_max_image card
    ⟨C₀, mem_filter.2 ⟨hC₀, haC₀, hbC₀⟩⟩
  obtain ⟨hUH, haU, hbU⟩ := mem_filter.1 hU
  have hAU : A ⊆ U := fun a' ha' => by
    obtain ⟨C, hC, haC, ha'C, hbC⟩ := h a ha a' ha' b hbA
    rcases hH.subset_or_subset_of_mem hC hUH haC haU with h' | h'
    · exact h' ha'C
    · exact (eq_of_subset_of_card_le h' (hUmax C (mem_filter.2 ⟨hC, haC, hbC⟩))) ▸ ha'C
  rcases hH.subset_or_subset_of_mem hLH hUH (hAL ha) haU with h' | h'
  · exact hbU (h' hbL)
  · exact hbU ((eq_of_subset_of_card_le h' (hLmin U (mem_filter.2 ⟨hUH, hAU⟩))).symm ▸ hbL)

end IsHierarchy

omit [Fintype X] in
theorem mem_restrictClusters {S : Finset X} {H : Finset (Finset X)} {C : Finset S} :
    C ∈ restrictClusters S H ↔ ∃ A ∈ H, (A ∩ S).Nonempty ∧ A.subtype (· ∈ S) = C := by
  unfold restrictClusters; simp only [mem_image, mem_filter, and_assoc]

omit [Fintype X] in
theorem subtype_nonempty_iff {S A : Finset X} :
    (A.subtype (· ∈ S)).Nonempty ↔ (A ∩ S).Nonempty :=
  ⟨fun ⟨⟨x, hxS⟩, hx⟩ => ⟨x, mem_inter.2 ⟨mem_subtype.1 hx, hxS⟩⟩,
    fun ⟨x, hx⟩ => ⟨⟨x, (mem_inter.1 hx).2⟩, mem_subtype.2 (mem_inter.1 hx).1⟩⟩

theorem subtype_compl {S : Finset X} (A : Finset X) :
    Aᶜ.subtype (· ∈ S) = (A.subtype (· ∈ S))ᶜ := by
  ext x; simp [mem_subtype, mem_compl]

theorem subtype_ne_univ_iff {S A : Finset X} :
    A.subtype (· ∈ S) ≠ univ ↔ (Aᶜ ∩ S).Nonempty := by
  rw [← subtype_nonempty_iff, subtype_compl, Ne, ← compl_eq_empty_iff,
    ← not_nonempty_iff_eq_empty, not_not]

omit [Fintype X] in
theorem subtype_mem_restrictClusters {S : Finset X} {H : Finset (Finset X)} {A : Finset X}
    (hA : A ∈ H) (hAS : (A ∩ S).Nonempty) : A.subtype (· ∈ S) ∈ restrictClusters S H :=
  mem_restrictClusters.2 ⟨A, hA, hAS, rfl⟩

theorem mem_unroot {G : Finset (Finset L)} {A : Finset L} :
    A ∈ unroot G ↔ (A ∈ G ∧ A ≠ univ) ∨ (Aᶜ ∈ G ∧ Aᶜ ≠ univ) :=
  absorb_mem_unroot

theorem compl_mem_unroot {G : Finset (Finset L)} {A : Finset L} :
    Aᶜ ∈ unroot G ↔ A ∈ unroot G := by
  rw [mem_unroot, mem_unroot, compl_compl, or_comm]

namespace SpeciesTree

@[simp] theorem restrict_clusters (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    (σ.restrict S hS).clusters = restrictClusters S σ.clusters := rfl

@[simp] theorem restrict_length (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    (σ.restrict S hS).length = σ.restrictLength S := rfl

theorem restrictLength_subtype_eq (σ : SpeciesTree X) {S A : Finset X} (hA : A ∈ σ.clusters)
    (hAu : A ≠ univ)
    (h : ∀ B ∈ σ.clusters, B.subtype (· ∈ S) = A.subtype (· ∈ S) → B = A) :
    σ.restrictLength S (A.subtype (· ∈ S)) = σ.length A := by
  unfold restrictLength
  rw [Finset.sum_eq_single_of_mem A (mem_filter.2 ⟨hA, hAu, rfl⟩)]
  exact fun B hB hBA => absurd (h B (mem_filter.1 hB).1 (mem_filter.1 hB).2.2) hBA

theorem mem_unroot_restrict (σ : SpeciesTree X) {S : Finset X} (hS : S.Nonempty) {C : Finset S} :
    C ∈ unroot (σ.restrict S hS).clusters ↔
      ∃ A ∈ unroot σ.clusters, (A ∩ S).Nonempty ∧ (Aᶜ ∩ S).Nonempty ∧ A.subtype (· ∈ S) = C := by
  rw [mem_unroot, restrict_clusters]
  constructor
  · rintro (⟨hC, hCu⟩ | ⟨hC, hCu⟩)
    · obtain ⟨A, hA, hAS, rfl⟩ := mem_restrictClusters.1 hC
      exact ⟨A, mem_unroot.2 (Or.inl ⟨hA, fun e => hCu (e ▸ subtype_univ _)⟩),
        hAS, subtype_ne_univ_iff.1 hCu, rfl⟩
    · obtain ⟨A, hA, hAS, hAC⟩ := mem_restrictClusters.1 hC
      refine ⟨Aᶜ, compl_mem_unroot.2 (mem_unroot.2
          (Or.inl ⟨hA, fun e => hCu (hAC ▸ e ▸ subtype_univ _)⟩)),
        subtype_ne_univ_iff.1 (hAC ▸ hCu), by rwa [compl_compl],
        by rw [subtype_compl, hAC, compl_compl]⟩
  · rintro ⟨A, hA, hAS, hAcS, rfl⟩
    rcases mem_unroot.1 hA with ⟨hA', -⟩ | ⟨hA', -⟩
    · exact Or.inl ⟨subtype_mem_restrictClusters hA' hAS, subtype_ne_univ_iff.2 hAcS⟩
    · refine Or.inr ⟨?_, ?_⟩
      · rw [← subtype_compl]; exact subtype_mem_restrictClusters hA' hAcS
      · rw [← subtype_compl]; exact subtype_ne_univ_iff.2 (by rwa [compl_compl])

theorem restrict_unrootedLength (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty)
    (C : Finset S) (hCne : C.Nonempty) (hCcne : Cᶜ.Nonempty) :
    (σ.restrict S hS).unrootedLength C =
      ∑ A ∈ σ.clusters with A ≠ univ ∧ (A.subtype (· ∈ S) = C ∨ A.subtype (· ∈ S) = Cᶜ),
        σ.length A := by
  have hCu : C ≠ univ := fun e => by rw [e, compl_univ] at hCcne; exact not_nonempty_empty hCcne
  have hCcu : Cᶜ ≠ univ := (compl_ne_univ_iff_nonempty C).2 hCne
  unfold unrootedLength
  rw [restrict_clusters, restrict_length]
  symm
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun A => A.subtype (· ∈ S))
    (t := (restrictClusters S σ.clusters).filter (fun D => D ≠ univ ∧ (D = C ∨ D = Cᶜ)))]
  · refine Finset.sum_congr rfl fun D hD => ?_
    unfold restrictLength
    rw [filter_filter]
    have hD' := (mem_filter.1 hD).2.2
    refine Finset.sum_congr (filter_congr fun A _ => ?_) fun _ _ => rfl
    exact ⟨fun ⟨⟨h2, _⟩, h3⟩ => ⟨h2, h3⟩, fun ⟨h2, h3⟩ => ⟨⟨h2, by rw [h3]; exact hD'⟩, h3⟩⟩
  · intro A hA
    obtain ⟨hA1, -, hA3⟩ := mem_filter.1 hA
    refine mem_filter.2 ⟨mem_restrictClusters.2 ⟨A, hA1, ?_, rfl⟩, ?_, hA3⟩
    · rw [← subtype_nonempty_iff]; rcases hA3 with h | h <;> rw [h] <;> assumption
    · rcases hA3 with h | h <;> rw [h] <;> assumption

theorem unrootedLength_compl (σ : SpeciesTree X) (A : Finset X) :
    σ.unrootedLength Aᶜ = σ.unrootedLength A := by
  unfold unrootedLength
  refine Finset.sum_congr (filter_congr fun B _ => ?_) fun _ _ => rfl
  rw [compl_compl, or_comm]

end SpeciesTree

end ADR11
