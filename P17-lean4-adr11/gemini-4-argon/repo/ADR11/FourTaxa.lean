module

public import ADR11.Rootings.Proofs
public import ADR11.MSC.Marginal

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

noncomputable abbrev Q4Exp (τ : SpeciesTree (Fin 4)) (L : ℝ) : Prop :=
  Q4Eq τ (1 - 2 / 3 * exp (-L)) (1 / 3 * exp (-L)) (1 / 3 * exp (-L))

theorem root_q4_one (τ : SpeciesTree (Fin 4)) {cs : List ℕ} (hτ : τ.clusters = h4 cs) (a : ℕ)
    (hS : (h4 cs).filter (fun C => C ≠ univ ∧ (C = {0, 1} ∨ C = {0, 1}ᶜ)) = {decC 4 a} := by decide)
    (hc : root_q4CertB cs [(-2 / 3, [(a, 1)]), (1, [])]
      [(1 / 3, [(a, 1)])] [(1 / 3, [(a, 1)])] = true := by decide +kernel) :
    Q4Exp τ (τ.unrootedLength {0, 1}) := by
  obtain ⟨h1, h2, h3⟩ := root_q4 τ hτ hc
  have hL : τ.unrootedLength {0, 1} = τ.length (decC 4 a) := by
    unfold SpeciesTree.unrootedLength; rw [hτ, hS, sum_singleton]
  simp only [Q4Exp, Q4Eq, h1, h2, h3, hL, evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil]
  push_cast
  exact ⟨by ring, by ring, by ring⟩

theorem root_q4_star (τ : SpeciesTree (Fin 4)) {cs : List ℕ} (hτ : τ.clusters = h4 cs)
    (hc : root_q4CertB cs [(1 / 3, [])] [(1 / 3, [])] [(1 / 3, [])] = true := by decide +kernel) :
    Q4Eq τ (1 / 3) (1 / 3) (1 / 3) := by
  obtain ⟨h1, h2, h3⟩ := root_q4 τ hτ hc
  simp only [Q4Eq, h1, h2, h3, evalPoly_cons, evalPoly_nil, monoVal_nil]
  push_cast
  exact ⟨by ring, by ring, by ring⟩

theorem fourTaxa_balanced (σ : SpeciesTree (Fin 4)) (hσ : σ.clusters = h4 [3, 12]) :
    Q4Exp σ (σ.length {0, 1} + σ.length {2, 3}) := by
  obtain ⟨h1, h2, h3⟩ :=
    root_q4 σ hσ (P₁ := [(-2 / 3, [(3, 1), (12, 1)]), (1, [])])
      (P₂ := [(1 / 3, [(3, 1), (12, 1)])])
      (P₃ := [(1 / 3, [(3, 1), (12, 1)])])
  simp only [Q4Exp, Q4Eq, h1, h2, h3, evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil,
    root_decC4_3, root_decC4_12, neg_add, exp_add]
  push_cast
  exact ⟨by ring, by ring, by ring⟩

theorem fourTaxa_caterpillar (σ : SpeciesTree (Fin 4)) (hσ : σ.clusters = h4 [3, 7]) :
    Q4Exp σ (σ.length {0, 1}) := by
  have hL : σ.unrootedLength {0, 1} = σ.length {0, 1} := by
    unfold SpeciesTree.unrootedLength
    rw [show σ.clusters.filter _ = {{0, 1}} by rw [hσ]; decide, sum_singleton]
  simpa only [hL] using root_q4_one σ hσ 3

private lemma n4_U4_one (τ : SpeciesTree (Fin 4)) (h : unroot τ.clusters = U4 1) :
    Q4Exp τ (τ.unrootedLength {0, 1}) := by
  have hm := mem_rootings4 τ 1 (by decide) h
  simp only [rootings4, mem_insert, mem_singleton] at hm
  rcases hm with hc | hc | hc | hc | hc | hc | hc <;>
    first | exact root_q4_one τ hc 3 | exact root_q4_one τ hc 12 | skip
  have hL : τ.unrootedLength {0, 1} = τ.length {0, 1} + τ.length {2, 3} := by
    unfold SpeciesTree.unrootedLength
    rw [show τ.clusters.filter _ = {{0, 1}, {2, 3}} by rw [hc]; decide, sum_pair (by decide)]
  simpa only [hL] using fourTaxa_balanced τ hc

private lemma n4_U4_zero (τ : SpeciesTree (Fin 4)) (h : unroot τ.clusters = U4 0) :
    Q4Eq τ (1 / 3) (1 / 3) (1 / 3) := by
  have hm := mem_rootings4 τ 0 (by decide) h
  simp only [rootings4, mem_insert, mem_singleton] at hm
  rcases hm with hc | hc | hc | hc | hc <;> exact root_q4_star τ hc

private lemma four_relabelFamily_treeOfClusters {Y : Type*} [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) (C : Finset (Finset X)) :
    relabelFamily e (treeOfClusters C) = treeOfClusters (relabelFamily e C) := by
  unfold treeOfClusters hierarchyOf
  rw [← unroot_relabelFamily]
  congr 1
  unfold relabelFamily
  rw [image_insert, image_union, image_image, Finset.map_univ_equiv]
  congr 2; ext D
  simp only [mem_image, mem_univ, true_and, Function.comp_apply, Finset.map_singleton]
  exact ⟨by rintro ⟨x, rfl⟩; exact ⟨e x, rfl⟩, fun ⟨y, h⟩ => ⟨e.symm y, by simp [← h]⟩⟩

private lemma four_dist_relabel (e : Fin 4 ≃ X) (σ : SpeciesTree X) (B : Finset X) :
    σ.unrootedDist id (treeOfClusters {B}) =
      (σ.relabel e.symm).unrootedDist id (treeOfClusters {B.map e.symm.toEmbedding}) := by
  rw [← SpeciesTree.unrootedDist_relabel σ e.symm (treeOfClusters {B}),
    four_relabelFamily_treeOfClusters, relabelFamily, image_singleton]

private lemma four_mem_unroot_relabel (e : Fin 4 ≃ X) (σ : SpeciesTree X) (B : Finset X) :
    B ∈ unroot σ.clusters ↔ B.map e.symm.toEmbedding ∈ unroot (σ.relabel e.symm).clusters := by
  rw [SpeciesTree.relabel_clusters, unroot_relabelFamily, map_mem_relabelFamily]

private lemma four_U4_zero_card_two : ∀ B : Finset (Fin 4), B ∈ U4 0 → #B ≠ 2 := by decide

private lemma four_U4_one_mem {A' : Finset (Fin 4)} (h1 : A' ∈ U4 1) (h2 : #A' = 2)
    (τ : SpeciesTree (Fin 4)) :
    τ.unrootedLength A' = τ.unrootedLength {0, 1} ∧
      treeOfClusters {A'} = treeOfClusters {{0, 1}} := by
  rcases (by decide : ∀ A' ∈ U4 1, #A' = 2 →
    (A' = {0, 1} ∨ A' = {0, 1}ᶜ) ∧ treeOfClusters {A'} = treeOfClusters {{0, 1}}) A' h1 h2 with
    ⟨rfl | rfl, hT⟩
  · exact ⟨rfl, hT⟩
  · exact ⟨τ.unrootedLength_compl _, hT⟩

theorem four_unrootedLength_pos (σ : SpeciesTree X) {A : Finset X}
    (hA : A ∈ unroot σ.clusters) : 0 < σ.unrootedLength A := by
  refine Finset.sum_pos (fun C hC => σ.length_pos C (mem_filter.1 hC).1 (mem_filter.1 hC).2.1) ?_
  rcases mem_unroot.1 hA with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨A, mem_filter.2 ⟨h1, h2, Or.inl rfl⟩⟩
  · exact ⟨Aᶜ, mem_filter.2 ⟨h1, h2, Or.inr rfl⟩⟩

theorem four_unrootedDist_eq_zero (hX : Fintype.card X = 4) (σ : SpeciesTree X)
    (T : Finset (Finset X)) (hT : ∀ B : Finset X, #B = 2 → T ≠ treeOfClusters {B}) :
    σ.unrootedDist id T = 0 := by
  obtain ⟨e, k, hk, he⟩ := exists_equiv_unroot_eq_U4 hX σ
  have key (C : Finset (Fin 4)) (hC : #C = 2) : relabelFamily e.symm T ≠ treeOfClusters {C} :=
    fun hTC => hT (C.map e.toEmbedding) (by rw [card_map, hC]) <| by
      have := congrArg (relabelFamily e.symm.symm) hTC
      rwa [relabelFamily_symm, four_relabelFamily_treeOfClusters, relabelFamily, image_singleton,
        Equiv.symm_symm] at this
  rw [← SpeciesTree.unrootedDist_relabel σ e.symm T]
  set τ := σ.relabel e.symm
  set S : Finset (Finset (Finset (Fin 4))) :=
    {treeOfClusters {{0, 1}}, treeOfClusters {{0, 2}}, treeOfClusters {{0, 3}}}
  have hU : relabelFamily e.symm T ∉ S := by
    simp only [S, mem_insert, mem_singleton, not_or]
    exact ⟨key _ (by decide), key _ (by decide), key _ (by decide)⟩
  have hS : ∑ V ∈ S, τ.unrootedDist id V = 1 := by
    rw [sum_insert (by decide), sum_insert (by decide), sum_singleton]
    rcases mem_insert.1 hk with rfl | hk
    · obtain ⟨h1, h2, h3⟩ := n4_U4_zero τ he; linarith
    · obtain ⟨h1, h2, h3⟩ := n4_U4_one τ (mem_singleton.1 hk ▸ he); linarith
  have h0 : ∑ V ∈ univ \ S, τ.unrootedDist id V = 0 := by
    linarith [sum_sdiff (subset_univ S) (f := τ.unrootedDist id), unrootedDist_sum τ id]
  exact (sum_eq_zero_iff_of_nonneg fun V _ => unrootedDist_nonneg τ id V).1 h0 _
    (mem_sdiff.2 ⟨mem_univ _, hU⟩)

theorem four_unrootedDist_ext (hX : Fintype.card X = 4) {σ σ' : SpeciesTree X}
    (h : ∀ B : Finset X, #B = 2 →
      σ.unrootedDist id (treeOfClusters {B}) = σ'.unrootedDist id (treeOfClusters {B})) :
    σ.unrootedDist id = σ'.unrootedDist id := by
  funext T
  by_cases hT : ∃ B : Finset X, #B = 2 ∧ T = treeOfClusters {B}
  · obtain ⟨B, hB, rfl⟩ := hT; exact h B hB
  · push Not at hT
    rw [four_unrootedDist_eq_zero hX σ T hT, four_unrootedDist_eq_zero hX σ' T hT]

theorem n4_unrootedDist_of_mem (hX : Fintype.card X = 4) (σ : SpeciesTree X) {A : Finset X}
    (hA : A ∈ unroot σ.clusters) (hA2 : #A = 2) :
    σ.unrootedDist id (treeOfClusters {A}) = 1 - 2 / 3 * exp (-σ.unrootedLength A) := by
  obtain ⟨e, k, hk, he⟩ := exists_equiv_unroot_eq_U4 hX σ
  have hA' : A.map e.symm.toEmbedding ∈ U4 k := he ▸ (four_mem_unroot_relabel e σ A).1 hA
  have hA'2 : #(A.map e.symm.toEmbedding) = 2 := by rw [card_map, hA2]
  rw [four_dist_relabel e σ A, ← SpeciesTree.unrootedLength_relabel σ e.symm A]
  rcases mem_insert.1 hk with rfl | hk
  · exact absurd hA'2 (four_U4_zero_card_two _ hA')
  · obtain ⟨hL, hT⟩ := four_U4_one_mem (mem_singleton.1 hk ▸ hA') hA'2 (σ.relabel e.symm)
    rw [hT, hL, (n4_U4_one _ (mem_singleton.1 hk ▸ he)).1]

theorem n4_unrootedDist_of_ne (hX : Fintype.card X = 4) (σ : SpeciesTree X) {A B : Finset X}
    (hA : A ∈ unroot σ.clusters) (hA2 : #A = 2) (hB2 : #B = 2) (hBA : B ≠ A) (hBA' : B ≠ Aᶜ) :
    σ.unrootedDist id (treeOfClusters {B}) = 1 / 3 * exp (-σ.unrootedLength A) := by
  obtain ⟨e, k, hk, he⟩ := exists_equiv_unroot_eq_U4 hX σ
  have hA' : A.map e.symm.toEmbedding ∈ U4 k := he ▸ (four_mem_unroot_relabel e σ A).1 hA
  have hA'2 : #(A.map e.symm.toEmbedding) = 2 := by rw [card_map, hA2]
  rw [four_dist_relabel e σ B, ← SpeciesTree.unrootedLength_relabel σ e.symm A]
  rcases mem_insert.1 hk with rfl | hk
  · exact absurd hA'2 (four_U4_zero_card_two _ hA')
  · obtain ⟨-, h2, h3⟩ := n4_U4_one _ (mem_singleton.1 hk ▸ he)
    rw [(four_U4_one_mem (mem_singleton.1 hk ▸ hA') hA'2 _).1]
    rcases (by decide : ∀ A' ∈ U4 1, ∀ B' : Finset (Fin 4), #A' = 2 → #B' = 2 →
      B' ≠ A' → B' ≠ A'ᶜ →
      treeOfClusters {B'} = treeOfClusters {{0, 2}} ∨
        treeOfClusters {B'} = treeOfClusters {{0, 3}})
      _ (mem_singleton.1 hk ▸ hA') _ hA'2 (by rw [card_map, hB2])
      (fun h => hBA (Finset.map_injective _ h))
      (by rw [msc_map_compl]; exact fun h => hBA' (Finset.map_injective _ h)) with h | h <;> rw [h]
    exacts [h2, h3]

theorem four_unrootedDist_of_star (hX : Fintype.card X = 4) (σ : SpeciesTree X)
    (hσ : ∀ A ∈ unroot σ.clusters, #A ≠ 2) {B : Finset X} (hB2 : #B = 2) :
    σ.unrootedDist id (treeOfClusters {B}) = 1 / 3 := by
  obtain ⟨e, k, hk, he⟩ := exists_equiv_unroot_eq_U4 hX σ
  rw [four_dist_relabel e σ B]
  simp only [mem_insert, mem_singleton] at hk
  rcases hk with rfl | rfl
  · obtain ⟨h1, h2, h3⟩ := n4_U4_zero _ he
    rcases (by decide : ∀ C : Finset (Fin 4), #C = 2 →
      treeOfClusters {C} = treeOfClusters {{0, 1}} ∨ treeOfClusters {C} = treeOfClusters {{0, 2}} ∨
        treeOfClusters {C} = treeOfClusters {{0, 3}})
      (B.map e.symm.toEmbedding) (by rw [card_map, hB2]) with h | h | h <;> rw [h]
    exacts [h1, h2, h3]
  · exfalso
    have h01 : ({0, 1} : Finset (Fin 4)) ∈ relabelFamily e.symm (unroot σ.clusters) := by
      rw [← unroot_relabelFamily, ← SpeciesTree.relabel_clusters, he]; decide
    exact hσ _ (mem_relabelFamily.1 h01) (by rw [card_map]; decide)

private theorem n4_mem_unroot_of_unrootedDist_eq (hX : Fintype.card X = 4)
    {σ σ' : SpeciesTree X} (h : σ.unrootedDist id = σ'.unrootedDist id) {A : Finset X}
    (hA : A ∈ unroot σ.clusters) (hA2 : #A = 2) :
    A ∈ unroot σ'.clusters ∧ σ.unrootedLength A = σ'.unrootedLength A := by
  have h1 := n4_unrootedDist_of_mem hX σ hA hA2
  have hlt : exp (-σ.unrootedLength A) < 1 :=
    exp_lt_one_iff.2 (neg_lt_zero.2 (four_unrootedLength_pos σ hA))
  rw [h] at h1
  by_cases hA' : A ∈ unroot σ'.clusters
  · refine ⟨hA', ?_⟩
    rw [n4_unrootedDist_of_mem hX σ' hA' hA2] at h1
    exact (neg_inj.1 (exp_eq_exp.1 (by linarith))).symm
  · exfalso
    by_cases hex : ∃ A' ∈ unroot σ'.clusters, #A' = 2
    · obtain ⟨A', hA'm, hA'2⟩ := hex
      rw [n4_unrootedDist_of_ne hX σ' hA'm hA'2 hA2
        (fun e => hA' (e ▸ hA'm)) (fun e => hA' (e ▸ compl_mem_unroot.2 hA'm))] at h1
      have : exp (-σ'.unrootedLength A') < 1 :=
        exp_lt_one_iff.2 (neg_lt_zero.2 (four_unrootedLength_pos σ' hA'm))
      linarith
    · push Not at hex
      rw [four_unrootedDist_of_star hX σ' hex hA2] at h1
      linarith

theorem unrootedDist_eq_iff_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' := by
  have hcard (A : Finset X) : #Aᶜ = 4 - #A := by rw [card_compl, hX]
  have hle (A : Finset X) : #A ≤ 4 := hX ▸ card_le_univ A
  constructor
  · intro h
    refine ⟨?_, fun A hA h2 h2' => (n4_mem_unroot_of_unrootedDist_eq hX h hA
      (by have := hcard A; have := hle A; omega)).2⟩
    ext A
    by_cases hA2 : #A = 2
    · exact ⟨fun hA => (n4_mem_unroot_of_unrootedDist_eq hX h hA hA2).1,
        fun hA => (n4_mem_unroot_of_unrootedDist_eq hX h.symm hA hA2).1⟩
    · rw [classify_mem_unroot_iff (Or.inl hX) σ, classify_mem_unroot_iff (Or.inl hX) σ']
      simp [mem_filter, hA2, show #Aᶜ ≠ 2 by have := hcard A; have := hle A; omega]
  · rintro ⟨hU, hL⟩
    have hlen (A) (hA : A ∈ unroot σ.clusters) (hA2 : #A = 2) :
        σ.unrootedLength A = σ'.unrootedLength A :=
      hL A hA (by omega) (by rw [hcard]; omega)
    refine four_unrootedDist_ext hX fun B hB2 => ?_
    by_cases hB : B ∈ unroot σ.clusters
    · rw [n4_unrootedDist_of_mem hX σ hB hB2, n4_unrootedDist_of_mem hX σ' (hU ▸ hB) hB2,
        hlen B hB hB2]
    · by_cases hex : ∃ A ∈ unroot σ.clusters, #A = 2
      · obtain ⟨A, hA, hA2⟩ := hex
        have hne1 : B ≠ A := fun e => hB (e ▸ hA)
        have hne2 : B ≠ Aᶜ := fun e => hB (e ▸ compl_mem_unroot.2 hA)
        rw [n4_unrootedDist_of_ne hX σ hA hA2 hB2 hne1 hne2,
          n4_unrootedDist_of_ne hX σ' (hU ▸ hA) hA2 hB2 hne1 hne2, hlen A hA hA2]
      · push Not at hex
        rw [four_unrootedDist_of_star hX σ hex hB2,
          four_unrootedDist_of_star hX σ' (hU ▸ hex) hB2]



local notation "sub" S:max A:max => Finset.subtype (· ∈ S) A

theorem nonempty_of_mem_unroot (σ : SpeciesTree X) {A : Finset X}
    (h : A ∈ unroot σ.clusters) : A.Nonempty := by
  rcases mem_unroot.1 h with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact σ.nonempty_of_mem A h1
  · rw [nonempty_iff_ne_empty]
    rintro rfl
    exact h2 compl_empty

theorem mem_unroot_iff_quartets (σ : SpeciesTree X) {A : Finset X} (hA : 2 ≤ #A)
    (hA' : 2 ≤ #Aᶜ) :
    A ∈ unroot σ.clusters ↔
      ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ Aᶜ, ∀ b' ∈ Aᶜ, a ≠ a' → b ≠ b' →
        ∃ C ∈ unroot σ.clusters, a ∈ C ∧ a' ∈ C ∧ b ∉ C ∧ b' ∉ C := by
  constructor
  · intro h a ha a' ha' b hb b' hb' _ _
    exact ⟨A, h, ha, ha', mem_compl.1 hb, mem_compl.1 hb'⟩
  intro hq
  obtain ⟨b₀, hb₀, b₁, hb₁, hb₀₁⟩ := one_lt_card.1 hA'
  obtain ⟨a, ha⟩ : A.Nonempty := card_pos.1 (by omega)
  have hnest : ∀ {C D}, C ∈ unroot σ.clusters → D ∈ unroot σ.clusters →
      b₀ ∉ C → b₀ ∉ D → a ∈ C → a ∈ D → C ⊆ D ∨ D ⊆ C := fun hC hD hC₀ hD₀ haC haD => by
    rcases laminar_of_mem_unroot σ hC hD with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (disjoint_left.1 h haC haD).elim
    · exact (hD₀ (h (mem_compl.2 hC₀))).elim
  have ha0 : b₀ ∉ ({a} : Finset X) := fun h => mem_compl.1 hb₀ (mem_singleton.1 h ▸ ha)
  obtain ⟨U, hU, hmax⟩ := ((unroot σ.clusters).filter fun C => b₀ ∉ C ∧ a ∈ C ∧ C ⊆ A).exists_max_image card
    ⟨{a}, mem_filter.2 ⟨mem_unroot.2 (Or.inl ⟨σ.singleton_mem a, fun e => ha0 (e ▸ mem_univ _)⟩),
      ha0, mem_singleton_self a, singleton_subset_iff.2 ha⟩⟩
  obtain ⟨hUF, hU₀, haU, hUA⟩ := mem_filter.1 hU
  rcases hUA.eq_or_ssubset with rfl | hUA
  · exact hUF
  · obtain ⟨a', ha'A, ha'U⟩ := exists_of_ssubset hUA
    have haa' : a ≠ a' := fun e => ha'U (e ▸ haU)
    obtain ⟨C₀, hC₀, haC₀, ha'C₀, -, hC₀₀⟩ := hq a ha a' ha'A b₁ hb₁ b₀ hb₀ haa' hb₀₁.symm
    obtain ⟨M, hM, hmin⟩ := ((unroot σ.clusters).filter fun C => b₀ ∉ C ∧ a ∈ C ∧ a' ∈ C).exists_min_image card
      ⟨C₀, mem_filter.2 ⟨hC₀, hC₀₀, haC₀, ha'C₀⟩⟩
    obtain ⟨hMF, hM₀, haM, ha'M⟩ := mem_filter.1 hM
    have hMA : M ⊆ A := fun b hbM => by_contra fun hbA => by
      obtain ⟨C, hCF, haC, ha'C, hbC, hC₀⟩ :=
        hq a ha a' ha'A b (mem_compl.2 hbA) b₀ hb₀ haa' (fun e => hM₀ (e ▸ hbM))
      rcases hnest hCF hMF hC₀ hM₀ haC haM with hCM | hMC
      · exact not_lt_of_ge (hmin C (mem_filter.2 ⟨hCF, hC₀, haC, ha'C⟩))
          (card_lt_card (hCM.ssubset_of_ne fun e => hbC (e ▸ hbM)))
      · exact hbC (hMC hbM)
    rcases hnest hUF hMF hU₀ hM₀ haU haM with hUM | hMU
    · exact absurd (card_lt_card (hUM.ssubset_of_ne fun e => ha'U (e ▸ ha'M)))
        (not_lt_of_ge (hmax M (mem_filter.2 ⟨hMF, hM₀, haM, hMA⟩)))
    · exact (ha'U (hMU ha'M)).elim

private theorem steel_exists_pair (σ : SpeciesTree X) {N : Finset X} (hN : 2 ≤ #N) :
    ∃ x ∈ N, ∃ y ∈ N, x ≠ y ∧ ∀ C ∈ σ.clusters, x ∈ C → y ∈ C → ¬ C ⊂ N := by
  obtain ⟨x, hx⟩ : N.Nonempty := card_pos.1 (by omega)
  obtain ⟨M, hM, hxM⟩ := σ.isHierarchy.exists_mem_childClusters hN hx
  obtain ⟨hMc, hMN, hmax⟩ := mem_childClusters.1 hM
  obtain ⟨y, hyN, hyM⟩ := exists_of_ssubset hMN
  refine ⟨x, hx, y, hyN, fun h => hyM (h ▸ hxM), fun C hC hxC hyC hCN => ?_⟩
  rcases σ.isHierarchy.subset_or_subset_of_mem hC hMc hxC hxM with h | h
  · exact hyM (h hyC)
  · exact hmax C hC (h.ssubset_of_ne fun e => hyM (e ▸ hyC)) hCN

private theorem steel_distinguishing_of_mem_clusters (σ : SpeciesTree X) {A : Finset X}
    (hA : A ∈ σ.clusters) (hAu : A ≠ univ) (hA₁ : 2 ≤ #A) (hA₂ : 2 ≤ #Aᶜ) :
    ∃ a ∈ A, ∃ a' ∈ A, ∃ b ∈ Aᶜ, ∃ b' ∈ Aᶜ, a ≠ a' ∧ b ≠ b' ∧
      ∀ C ∈ unroot σ.clusters, a ∈ C → a' ∈ C → b ∉ C → b' ∉ C → C = A := by
  obtain ⟨a, ha, a', ha', haa, hpair⟩ := steel_exists_pair σ hA₁
  have hup (C) (hC : C ∈ σ.clusters) (h1 : a ∈ C) (h2 : a' ∈ C) : A ⊆ C :=
    (σ.isHierarchy.subset_or_subset_of_mem hC hA h1 ha).elim
      (fun h => h.eq_or_ssubset.elim (·.symm.subset) fun h => (hpair C hC h1 h2 h).elim) id
  obtain ⟨P, hP, hPmin⟩ := exists_min_image (σ.clusters.filter fun C => A ⊂ C) card
    ⟨univ, mem_filter.2 ⟨σ.univ_mem, ssubset_univ_iff.2 hAu⟩⟩
  obtain ⟨hPc, hAP⟩ := mem_filter.1 hP
  have hPle (C) (hC : C ∈ σ.clusters) (hAC : A ⊂ C) : P ⊆ C :=
    (σ.isHierarchy.subset_or_subset_of_mem hC hPc (hAC.1 ha) (hAP.1 ha)).elim
      (fun h => (eq_of_subset_of_card_le h (hPmin C (mem_filter.2 ⟨hC, hAC⟩))).symm.subset) id
  obtain ⟨b, hb, b', hb', hbb, hP1, hP2⟩ : ∃ b ∈ Aᶜ, ∃ b' ∈ Aᶜ, b ≠ b' ∧
      (∀ C ∈ σ.clusters, A ⊂ C → b ∈ C ∨ b' ∈ C) ∧
      (∀ D ∈ σ.clusters, b ∈ D → b' ∈ D → ¬ D ⊂ Aᶜ) := by
    by_cases hPu : P = univ
    · obtain ⟨b, hb, b', hb', hbb, h⟩ := steel_exists_pair σ hA₂
      exact ⟨b, hb, b', hb', hbb, fun C hC hAC => Or.inl ((hPu ▸ hPle C hC hAC) (mem_univ b)), h⟩
    · obtain ⟨b, hbP, hbA⟩ := exists_of_ssubset hAP
      obtain ⟨b', hb'⟩ := nonempty_iff_ne_empty.2 (mt (compl_eq_empty_iff P).1 hPu)
      rw [mem_compl] at hb'
      exact ⟨b, mem_compl.2 hbA, b', mem_compl.2 (fun h => hb' (hAP.1 h)),
        fun e => hb' (e ▸ hbP), fun C hC hAC => Or.inl (hPle C hC hAC hbP),
        fun D hD hbD hb'D hDA =>
          (σ.isHierarchy.subset_or_subset_of_mem hD hPc hbD hbP).elim
            (fun h => hb' (h hb'D)) fun h => mem_compl.1 (hDA.1 (h (hAP.1 ha))) ha⟩
  refine ⟨a, ha, a', ha', b, hb, b', hb', haa, hbb, fun C hC haC ha'C hbC hb'C => ?_⟩
  rcases mem_unroot.1 hC with ⟨hC1, -⟩ | ⟨hC1, -⟩
  · exact by_contra fun hne =>
      (hP1 C hC1 ((hup C hC1 haC ha'C).ssubset_of_ne (Ne.symm hne))).elim hbC hb'C
  · have hDA : Cᶜ ⊆ Aᶜ := by
      rcases σ.laminar Cᶜ hC1 A hA with h | h | h
      · exact absurd (h (mem_compl.2 hbC)) (mem_compl.1 hb)
      · exact absurd haC (mem_compl.1 (h ha))
      · exact subset_compl_iff_disjoint_right.2 h
    exact compl_injective (by_contra fun hne =>
      hP2 Cᶜ hC1 (mem_compl.2 hbC) (mem_compl.2 hb'C) (hDA.ssubset_of_ne hne))

theorem exists_distinguishing_quartet (σ : SpeciesTree X) {A : Finset X}
    (hA : A ∈ unroot σ.clusters) (hA₁ : 2 ≤ #A) (hA₂ : 2 ≤ #Aᶜ) :
    ∃ a ∈ A, ∃ a' ∈ A, ∃ b ∈ Aᶜ, ∃ b' ∈ Aᶜ, a ≠ a' ∧ b ≠ b' ∧
      ∀ C ∈ unroot σ.clusters, a ∈ C → a' ∈ C → b ∉ C → b' ∉ C → C = A := by
  rcases mem_unroot.1 hA with ⟨hA1, hA2⟩ | ⟨hA1, hA2⟩
  · exact steel_distinguishing_of_mem_clusters σ hA1 hA2 hA₁ hA₂
  · obtain ⟨a, ha, a', ha', b, hb, b', hb', haa, hbb, h⟩ :=
      steel_distinguishing_of_mem_clusters σ hA1 hA2 hA₂ (by rwa [compl_compl])
    rw [compl_compl] at hb hb'
    exact ⟨b, hb, b', hb', a, ha, a', ha', hbb, haa, fun C hC hbC hb'C haC ha'C =>
      compl_injective (h Cᶜ (compl_mem_unroot.2 hC) (mem_compl.2 haC) (mem_compl.2 ha'C)
        (fun h' => mem_compl.1 h' hbC) (fun h' => mem_compl.1 h' hb'C))⟩

theorem unrootedDist_restrict_eq {σ σ' : SpeciesTree X}
    (h : σ.unrootedDist id = σ'.unrootedDist id) (S : Finset X) (hS : S.Nonempty) :
    (σ.restrict S hS).unrootedDist id = (σ'.restrict S hS).unrootedDist id := by
  have key (τ : SpeciesTree X) (T') : (τ.restrict S hS).unrootedDist id T' =
      τ.unrootedDist (id ∘ Function.Embedding.subtype (· ∈ S)) T' := by
    simp [SpeciesTree.unrootedDist, τ.rootedDist_restrict S hS id]
  ext T'; rw [key, key, σ.unrootedDist_comp_embedding, σ'.unrootedDist_comp_embedding, h]

theorem quart_card_quartet {A : Finset X} {a a' b b' : X} (ha : a ∈ A) (ha' : a' ∈ A)
    (hb : b ∉ A) (hb' : b' ∉ A) (haa : a ≠ a') (hbb : b ≠ b') :
    #({a, a', b, b'} : Finset X) = 4 := by
  have hne : a ≠ b ∧ a ≠ b' ∧ a' ≠ b ∧ a' ≠ b' :=
    ⟨by rintro rfl; exact hb ha, by rintro rfl; exact hb' ha,
     by rintro rfl; exact hb ha', by rintro rfl; exact hb' ha'⟩
  rw [card_insert_of_notMem (by simp [haa, hne]),
    card_insert_of_notMem (by simp [hne]), card_pair hbb]

private theorem quart_unroot_subset (σ σ' : SpeciesTree X)
    (h : ∀ Q : Finset X, ∀ hQ : Q.Nonempty, #Q = 4 →
      unroot (σ.restrict Q hQ).clusters = unroot (σ'.restrict Q hQ).clusters) :
    unroot σ.clusters ⊆ unroot σ'.clusters := by
  intro A hA
  have hAne := nonempty_of_mem_unroot σ hA
  have hAcne := nonempty_of_mem_unroot σ (compl_mem_unroot.2 hA)
  by_cases h1 : #A ≤ 1
  · obtain ⟨x, rfl⟩ := card_eq_one.1 (le_antisymm h1 (card_pos.2 hAne))
    refine mem_unroot.2 (Or.inl ⟨σ'.singleton_mem x, ?_⟩)
    intro hu; rw [hu, compl_univ] at hAcne; exact not_nonempty_empty hAcne
  by_cases h2 : #Aᶜ ≤ 1
  · obtain ⟨x, hx⟩ := card_eq_one.1 (le_antisymm h2 (card_pos.2 hAcne))
    refine mem_unroot.2 (Or.inr ⟨hx ▸ σ'.singleton_mem x, ?_⟩)
    intro hu; exact hAne.ne_empty (by rw [← compl_compl A, hu, compl_univ])
  rw [mem_unroot_iff_quartets σ' (by omega) (by omega)]
  intro a ha a' ha' b hb b' hb' haa hbb
  rw [mem_compl] at hb hb'
  set Q : Finset X := {a, a', b, b'}
  have hQ : Q.Nonempty := insert_nonempty _ _
  have hU := h Q hQ (quart_card_quartet ha ha' hb hb' haa hbb)
  obtain ⟨C, hC, -, -, hCA⟩ := (σ'.mem_unroot_restrict Q hQ).1 (hU ▸ (σ.mem_unroot_restrict Q hQ).2
    ⟨A, hA, ⟨a, mem_inter.2 ⟨ha, by simp [Q]⟩⟩, ⟨b, mem_inter.2 ⟨mem_compl.2 hb, by simp [Q]⟩⟩, rfl⟩)
  exact ⟨C, hC, (mem_iff_of_subtype_eq hCA (by simp [Q])).2 ha,
    (mem_iff_of_subtype_eq hCA (by simp [Q])).2 ha',
    fun h => hb ((mem_iff_of_subtype_eq hCA (by simp [Q])).1 h),
    fun h => hb' ((mem_iff_of_subtype_eq hCA (by simp [Q])).1 h)⟩

theorem sameUnrootedMetricTree_of_unrootedDist_eq (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameUnrootedMetricTree σ' := by
  have h4 (Q : Finset X) (hQ : Q.Nonempty) (hQ4 : #Q = 4) :
      (σ.restrict Q hQ).SameUnrootedMetricTree (σ'.restrict Q hQ) :=
    (unrootedDist_eq_iff_four (by simpa using hQ4) _ _).1 (unrootedDist_restrict_eq h Q hQ)
  have hU : unroot σ.clusters = unroot σ'.clusters :=
    Subset.antisymm (quart_unroot_subset σ σ' fun Q hQ hQ4 => (h4 Q hQ hQ4).1)
      (quart_unroot_subset σ' σ fun Q hQ hQ4 => (h4 Q hQ hQ4).1.symm)
  refine ⟨hU, fun A hA hA₁ hA₂ => ?_⟩
  obtain ⟨a, ha, a', ha', b, hb, b', hb', haa, hbb, huniq⟩ :=
    exists_distinguishing_quartet σ hA hA₁ hA₂
  rw [mem_compl] at hb hb'
  set Q : Finset X := {a, a', b, b'}
  have hQ : Q.Nonempty := insert_nonempty _ _
  have haQ : a ∈ Q := by simp [Q]
  have ha'Q : a' ∈ Q := by simp [Q]
  have hbQ : b ∈ Q := by simp [Q]
  have hb'Q : b' ∈ Q := by simp [Q]
  obtain ⟨_, hLQ⟩ := h4 Q hQ (quart_card_quartet ha ha' hb hb' haa hbb)
  have hC₀ : sub Q A ∈ unroot (σ.restrict Q hQ).clusters :=
    (σ.mem_unroot_restrict Q hQ).2
      ⟨A, hA, ⟨a, mem_inter.2 ⟨ha, haQ⟩⟩, ⟨b, mem_inter.2 ⟨mem_compl.2 hb, hbQ⟩⟩, rfl⟩
  have hC₀₁ : 2 ≤ #(sub Q A) :=
    one_lt_card.2 ⟨⟨a, haQ⟩, mem_subtype.2 ha, ⟨a', ha'Q⟩, mem_subtype.2 ha',
      fun h => haa (congrArg Subtype.val h)⟩
  have hC₀₂ : 2 ≤ #(sub Q A)ᶜ :=
    one_lt_card.2 ⟨⟨b, hbQ⟩, by simp [hb], ⟨b', hb'Q⟩, by simp [hb'],
      fun h => hbb (congrArg Subtype.val h)⟩
  have hlen (τ : SpeciesTree X)
      (huniqτ : ∀ C ∈ unroot τ.clusters, a ∈ C → a' ∈ C → b ∉ C → b' ∉ C → C = A) :
      (τ.restrict Q hQ).unrootedLength (sub Q A) = τ.unrootedLength A := by
    have heq {C} (hC : C ∈ unroot τ.clusters) (h1 : sub Q C = sub Q A) : C = A :=
      huniqτ C hC ((mem_iff_of_subtype_eq h1 haQ).2 ha) ((mem_iff_of_subtype_eq h1 ha'Q).2 ha')
        (fun h => hb ((mem_iff_of_subtype_eq h1 hbQ).1 h))
        (fun h => hb' ((mem_iff_of_subtype_eq h1 hb'Q).1 h))
    rw [τ.restrict_unrootedLength Q hQ _ hC₀₁ hC₀₂, SpeciesTree.unrootedLength]
    refine Finset.sum_congr (filter_congr fun B hB => and_congr_right fun hBu =>
      ⟨?_, by rintro (rfl | rfl); exacts [Or.inl rfl, Or.inr (subtype_compl _)]⟩) fun _ _ => rfl
    rintro (h1 | h1)
    · exact Or.inl (heq (mem_unroot.2 (Or.inl ⟨hB, hBu⟩)) h1)
    · exact Or.inr (compl_eq_comm.1 (heq (compl_mem_unroot.2 (mem_unroot.2 (Or.inl ⟨hB, hBu⟩)))
        (by rw [subtype_compl, h1, compl_compl]))).symm
  rw [← hlen σ huniq, ← hlen σ' (hU ▸ huniq)]
  exact hLQ _ hC₀ hC₀₁ hC₀₂

theorem rl_compl_nonempty {A : Finset X} (hAu : A ≠ univ) : Aᶜ.Nonempty :=
  nonempty_iff_ne_empty.2 (mt (compl_eq_empty_iff A).1 hAu)

theorem rl_eq_of_mem_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {R R' : Finset X} (hR : R ∈ childClusters H univ) (hR' : R' ∈ childClusters H univ) {x : X}
    (hx : x ∈ R) (hx' : x ∈ R') : R = R' := by
  by_contra hne
  exact disjoint_left.1 (hH.disjoint_of_mem_childClusters hR hR' hne) hx hx'

theorem rl_ne_univ_of_mem_childClusters {H : Finset (Finset X)} {R : Finset X}
    (hR : R ∈ childClusters H univ) : R ≠ univ :=
  ssubset_univ_iff.1 (mem_childClusters.1 hR).2.1

theorem rl_eq_of_unroot_eq {H H' : Finset (Finset X)} (hH : IsHierarchy H)
    (hH' : IsHierarchy H') (hU : unroot H = unroot H')
    (hR : childClusters H univ = childClusters H' univ) : H = H' := by
  have hiff {G : Finset (Finset X)} (hG : IsHierarchy G) {C : Finset X} :
      C ∈ G ↔ C = univ ∨ (C ∈ unroot G ∧ ∃ R ∈ childClusters G univ, C ⊆ R) :=
    ⟨fun hC => (eq_or_ne C univ).imp_right fun hCu => ⟨mem_unroot.2 (Or.inl ⟨hC, hCu⟩),
        hG.exists_mem_childClusters_superset hC (ssubset_univ_iff.2 hCu)⟩,
     by rintro (rfl | ⟨hC, R, hR, hCR⟩)
        · exact hG.1
        · rcases mem_unroot.1 hC with ⟨h, -⟩ | ⟨h, hu⟩
          · exact h
          · have hRG := (mem_childClusters.1 hR).1
            rcases hG.2.2.2 _ h R hRG with h' | h' | h'
            · exact absurd (eq_univ_of_forall fun x => by_contra fun hx =>
                hx (h' (compl_subset_compl.2 hCR (mem_compl.2 hx))))
                (rl_ne_univ_of_mem_childClusters hR)
            · exact absurd (eq_univ_of_forall fun x => mem_compl.2 fun hx =>
                mem_compl.1 (h' (hCR hx)) hx) hu
            · rwa [compl_inj_iff.1 (Subset.antisymm (subset_compl_iff_disjoint_right.2 h')
                (compl_subset_compl.2 hCR))]⟩
  ext C; rw [hiff hH, hiff hH', hU, hR]

theorem rl_mem_childClusters_restrict_iff (σ : SpeciesTree X) {S : Finset X} (hS : S.Nonempty)
    (hmrca : ∀ R ∈ childClusters σ.clusters univ, ¬ S ⊆ R) {C : Finset S} :
    C ∈ childClusters (σ.restrict S hS).clusters univ ↔
      ∃ R ∈ childClusters σ.clusters univ, (R ∩ S).Nonempty ∧ sub S R = C := by
  have hH := σ.isHierarchy
  have htr : ∀ R ∈ childClusters σ.clusters univ, (R ∩ S).Nonempty →
      sub S R ∈ (σ.restrict S hS).clusters ∧ sub S R ⊂ univ := fun R hR hRS =>
    ⟨subtype_mem_restrictClusters (mem_childClusters.1 hR).1 hRS,
      ssubset_univ_iff.2 (subtype_ne_univ_iff.2 <|
        let ⟨y, hyS, hyR⟩ := not_subset.1 (hmrca R hR); ⟨y, mem_inter.2 ⟨mem_compl.2 hyR, hyS⟩⟩)⟩
  have hsup : ∀ B ∈ σ.clusters, B ≠ univ → ∃ R ∈ childClusters σ.clusters univ, B ⊆ R :=
    fun B hB hBu => hH.exists_mem_childClusters_superset hB (ssubset_univ_iff.2 hBu)
  constructor
  · intro hC
    obtain ⟨hCcl, hCu, hmax⟩ := mem_childClusters.1 hC
    obtain ⟨B, hB, ⟨y, hy⟩, rfl⟩ := mem_restrictClusters.1 hCcl
    obtain ⟨R, hR, hBR⟩ := hsup B hB (by rintro rfl; exact (ssubset_univ_iff.1 hCu) (subtype_univ _))
    have hRS : (R ∩ S).Nonempty := ⟨y, mem_inter.2 ⟨hBR (mem_inter.1 hy).1, (mem_inter.1 hy).2⟩⟩
    obtain ⟨hRcl, hRu⟩ := htr R hR hRS
    exact ⟨R, hR, hRS, (subtype_mono hBR).eq_or_ssubset.elim Eq.symm fun h =>
      absurd hRu (hmax _ hRcl h)⟩
  · rintro ⟨R, hR, hRS, rfl⟩
    obtain ⟨hRcl, hRu⟩ := htr R hR hRS
    refine mem_childClusters.2 ⟨hRcl, hRu, fun D hD hRD hDu => ?_⟩
    obtain ⟨B, hB, -, rfl⟩ := mem_restrictClusters.1 hD
    obtain ⟨R', hR', hBR'⟩ := hsup B hB (by rintro rfl; exact (ssubset_univ_iff.1 hDu) (subtype_univ _))
    obtain ⟨y, hy⟩ := hRS
    have hyB : y ∈ B := mem_subtype.1
      (hRD.subset (mem_subtype.2 (mem_inter.1 hy).1 : (⟨y, (mem_inter.1 hy).2⟩ : S) ∈ _))
    exact not_subset_of_ssubset hRD
      (rl_eq_of_mem_childClusters hH hR hR' (mem_inter.1 hy).1 (hBR' hyB) ▸ subtype_mono hBR')

theorem rl_exists_five (hX : 5 ≤ Fintype.card X) {T : Finset X} (hT : #T ≤ 5) :
    ∃ S, T ⊆ S ∧ #S = 5 :=
  let ⟨S, hTS, _, hS⟩ := exists_subsuperset_card_eq (subset_univ T) hT (by rwa [card_univ])
  ⟨S, hTS, hS⟩

private theorem rl_of_three (hX : 5 ≤ Fintype.card X) (σ : SpeciesTree X) {A : Finset X}
    {x y z : X} (hxA : x ∈ A) (hyA : y ∈ Aᶜ)
    (hmrca : ∀ R ∈ childClusters σ.clusters univ, ¬ (x ∈ R ∧ y ∈ R ∧ z ∈ R))
    (hnot : ∀ R' ∈ childClusters σ.clusters univ, x ∈ R' → y ∉ R' → (z ∈ R' ↔ z ∈ A) → False) :
    ∃ S : Finset X, ∃ hS : S.Nonempty, #S = 5 ∧ (A ∩ S).Nonempty ∧ (Aᶜ ∩ S).Nonempty ∧
      sub S A ∉ childClusters (σ.restrict S hS).clusters univ := by
  obtain ⟨S, hTS, hS5⟩ := rl_exists_five hX (T := {x, y, z}) (card_le_three.trans (by norm_num))
  have hxS : x ∈ S := hTS (by simp)
  have hyS : y ∈ S := hTS (by simp)
  have hzS : z ∈ S := hTS (by simp)
  refine ⟨S, ⟨x, hxS⟩, hS5, ⟨x, mem_inter.2 ⟨hxA, hxS⟩⟩, ⟨y, mem_inter.2 ⟨hyA, hyS⟩⟩, fun hC => ?_⟩
  obtain ⟨R', hR', -, hR'eq⟩ := (rl_mem_childClusters_restrict_iff σ ⟨x, hxS⟩
    (fun R hR hSR => hmrca R hR ⟨hSR hxS, hSR hyS, hSR hzS⟩)).1 hC
  exact hnot R' hR' ((mem_iff_of_subtype_eq hR'eq hxS).2 hxA)
    (fun h => mem_compl.1 hyA ((mem_iff_of_subtype_eq hR'eq hyS).1 h))
    (mem_iff_of_subtype_eq hR'eq hzS)

theorem rl_exists_insert_meets (hX : 5 ≤ Fintype.card X) {Q R : Finset X} (hQ : #Q = 4)
    (hR : R.Nonempty) (hRc : Rᶜ.Nonempty) :
    ∃ x ∉ Q, (R ∩ insert x Q).Nonempty ∧ (Rᶜ ∩ insert x Q).Nonempty := by
  have hins {P : Finset X} {x : X} : (P ∩ Q).Nonempty → (P ∩ insert x Q).Nonempty :=
    fun ⟨y, hy⟩ => ⟨y, mem_inter.2 ⟨(mem_inter.1 hy).1, mem_insert_of_mem (mem_inter.1 hy).2⟩⟩
  have hnew {P : Finset X} {x : X} (hx : x ∈ P) : (P ∩ insert x Q).Nonempty :=
    ⟨_, mem_inter.2 ⟨hx, mem_insert_self _ _⟩⟩
  by_cases h1 : (R ∩ Q).Nonempty
  · by_cases h2 : (Rᶜ ∩ Q).Nonempty
    · obtain ⟨x, hx⟩ : Qᶜ.Nonempty := by rw [← card_pos, card_compl]; omega
      exact ⟨x, mem_compl.1 hx, hins h1, hins h2⟩
    · obtain ⟨x, hx⟩ := hRc
      exact ⟨x, fun hxQ => h2 ⟨x, mem_inter.2 ⟨hx, hxQ⟩⟩, hins h1, hnew hx⟩
  · obtain ⟨x, hx⟩ := hR
    obtain ⟨q, hq⟩ : Q.Nonempty := card_pos.1 (by omega)
    exact ⟨x, fun hxQ => h1 ⟨x, mem_inter.2 ⟨hx, hxQ⟩⟩, hnew hx,
      hins ⟨q, mem_inter.2 ⟨mem_compl.2 fun hqR => h1 ⟨q, mem_inter.2 ⟨hqR, hq⟩⟩, hq⟩⟩⟩

theorem rl_nb_exists_five_not_mem_childClusters (hX : 5 ≤ Fintype.card X) (σ : SpeciesTree X)
    {A : Finset X} (hA : A ∈ unroot σ.clusters) (hAR : A ∉ childClusters σ.clusters univ) :
    ∃ S : Finset X, ∃ hS : S.Nonempty, #S = 5 ∧ (A ∩ S).Nonempty ∧ (Aᶜ ∩ S).Nonempty ∧
      sub S A ∉ childClusters (σ.restrict S hS).clusters univ := by
  have hH := σ.isHierarchy
  have hAne := nonempty_of_mem_unroot σ hA
  have hAcne := nonempty_of_mem_unroot σ (compl_mem_unroot.2 hA)
  have hroot (x : X) := hH.exists_mem_childClusters (by rw [card_univ]; omega) (mem_univ x)
  have hother {R : Finset X} {ℓ : X} (hℓR : ℓ ∈ R) (hRℓ : R ≠ {ℓ}) : ∃ m ∈ R, m ≠ ℓ := by
    by_contra! hcon; exact hRℓ (eq_singleton_iff_unique_mem.2 ⟨hℓR, hcon⟩)
  by_cases hA1 : #A = 1
  · obtain ⟨ℓ, rfl⟩ := card_eq_one.1 hA1
    obtain ⟨R, hR, hℓR⟩ := hroot ℓ
    obtain ⟨m, hmR, hmℓ⟩ := hother hℓR fun e => hAR (e ▸ hR)
    obtain ⟨r, hr⟩ := rl_compl_nonempty (rl_ne_univ_of_mem_childClusters hR)
    exact rl_of_three hX σ (mem_singleton_self ℓ) (mem_compl.2 (by simpa using hmℓ)) (z := r)
      (fun R₀ hR₀ ⟨h1, _, h3⟩ => mem_compl.1 hr (rl_eq_of_mem_childClusters hH hR hR₀ hℓR h1 ▸ h3))
      (fun R' hR' h1 h2 _ => h2 (rl_eq_of_mem_childClusters hH hR hR' hℓR h1 ▸ hmR))
  by_cases hAc1 : #Aᶜ = 1
  · obtain ⟨ℓ, hℓ⟩ := card_eq_one.1 hAc1
    have hmemA (y : X) : y ∈ A ↔ y ≠ ℓ := by
      rw [← not_iff_not, not_not, ← mem_compl, hℓ, mem_singleton]
    have hℓA : ℓ ∈ Aᶜ := hℓ ▸ mem_singleton_self ℓ
    obtain ⟨R, hR, hℓR⟩ := hroot ℓ
    by_cases hRℓ : R = {ℓ}
    · subst hRℓ
      obtain ⟨r₁, hr₁A⟩ := hAne
      obtain ⟨R₁, hR₁, hr₁R₁⟩ := hroot r₁
      have hℓR₁ : ℓ ∉ R₁ := fun h => (hmemA r₁).1 hr₁A <| mem_singleton.1 <|
        rl_eq_of_mem_childClusters hH hR hR₁ (mem_singleton_self ℓ) h ▸ hr₁R₁
      obtain ⟨r₂, hr₂A, hr₂R₁⟩ : ∃ r₂ ∈ A, r₂ ∉ R₁ := by
        by_contra! hcon
        exact hAR (Subset.antisymm (fun y hy => (hmemA y).2 fun e => hℓR₁ (e ▸ hy)) hcon ▸ hR₁)
      exact rl_of_three hX σ hr₁A hℓA (z := r₂)
        (fun R₀ hR₀ ⟨h1, h2, _⟩ => hℓR₁ (rl_eq_of_mem_childClusters hH hR₁ hR₀ hr₁R₁ h1 ▸ h2))
        (fun R' hR' h1 _ h3 => hr₂R₁ (rl_eq_of_mem_childClusters hH hR₁ hR' hr₁R₁ h1 ▸ h3.2 hr₂A))
    · obtain ⟨m, hmR, hmℓ⟩ := hother hℓR hRℓ
      obtain ⟨r, hr⟩ := rl_compl_nonempty (rl_ne_univ_of_mem_childClusters hR)
      exact rl_of_three hX σ ((hmemA m).2 hmℓ) hℓA (z := r)
        (fun R₀ hR₀ ⟨_, h2, h3⟩ => mem_compl.1 hr (rl_eq_of_mem_childClusters hH hR hR₀ hℓR h2 ▸ h3))
        (fun R' hR' h1 h2 _ => h2 (rl_eq_of_mem_childClusters hH hR hR' hmR h1 ▸ hℓR))
  have hA2 : 2 ≤ #A := by have := card_pos.2 hAne; omega
  have hAc2 : 2 ≤ #Aᶜ := by have := card_pos.2 hAcne; omega
  obtain ⟨a, ha, a', ha', b, hb, b', hb', haa, hbb, hQ⟩ :=
    exists_distinguishing_quartet σ hA hA2 hAc2
  rw [mem_compl] at hb hb'
  have hQ4 := quart_card_quartet ha ha' hb hb' haa hbb
  obtain ⟨R₀, hR₀, haR₀⟩ := hroot a
  obtain ⟨x, hxQ, ⟨y, hy⟩, ⟨z, hz⟩⟩ := rl_exists_insert_meets hX hQ4 ⟨a, haR₀⟩
    (rl_compl_nonempty (rl_ne_univ_of_mem_childClusters hR₀))
  set S : Finset X := insert x {a, a', b, b'}
  have hS : S.Nonempty := insert_nonempty _ _
  refine ⟨S, hS, by rw [card_insert_of_notMem hxQ, hQ4],
    ⟨a, mem_inter.2 ⟨ha, by simp [S]⟩⟩, ⟨b, mem_inter.2 ⟨mem_compl.2 hb, by simp [S]⟩⟩,
    fun hC => ?_⟩
  obtain ⟨R', hR', -, hR'eq⟩ := (rl_mem_childClusters_restrict_iff σ hS fun R' hR' hSR' =>
    mem_compl.1 (mem_inter.1 hz).1
      (rl_eq_of_mem_childClusters hH hR₀ hR' (mem_inter.1 hy).1 (hSR' (mem_inter.1 hy).2) ▸
        hSR' (mem_inter.1 hz).2)).1 hC
  have hmem (w : X) (hw : w ∈ S) : w ∈ R' ↔ w ∈ A := mem_iff_of_subtype_eq hR'eq hw
  exact hAR (hQ R' (mem_unroot.2 (Or.inl ⟨(mem_childClusters.1 hR').1,
      rl_ne_univ_of_mem_childClusters hR'⟩))
    ((hmem a (by simp [S])).2 ha) ((hmem a' (by simp [S])).2 ha')
    (fun h => hb ((hmem b (by simp [S])).1 h))
    (fun h => hb' ((hmem b' (by simp [S])).1 h)) ▸ hR')

theorem rl_nb_childClusters_univ_eq (hX : 5 ≤ Fintype.card X) {σ σ' : SpeciesTree X}
    (hU : unroot σ.clusters = unroot σ'.clusters)
    (h5 : ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
      (σ.restrict S hS).clusters = (σ'.restrict S hS).clusters) :
    childClusters σ.clusters univ = childClusters σ'.clusters univ := by
  have hiff (τ : SpeciesTree X) {A : Finset X} (hA : A ∈ unroot τ.clusters) :
      A ∈ childClusters τ.clusters univ ↔
        ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 → (A ∩ S).Nonempty → (Aᶜ ∩ S).Nonempty →
          sub S A ∈ childClusters (τ.restrict S hS).clusters univ :=
    ⟨fun hAR S hS _ ⟨y, hy⟩ ⟨z, hz⟩ =>
      (rl_mem_childClusters_restrict_iff τ hS fun R hR hSR =>
        mem_compl.1 (mem_inter.1 hz).1 (rl_eq_of_mem_childClusters τ.isHierarchy hAR hR
          (mem_inter.1 hy).1 (hSR (mem_inter.1 hy).2) ▸ hSR (mem_inter.1 hz).2)).2
        ⟨A, hAR, ⟨y, hy⟩, rfl⟩,
     fun h => by_contra fun hAR =>
      let ⟨S, hS, hS5, hAS, hAcS, hnot⟩ := rl_nb_exists_five_not_mem_childClusters hX τ hA hAR
      hnot (h S hS hS5 hAS hAcS)⟩
  have key (τ τ' : SpeciesTree X) (hU : unroot τ.clusters = unroot τ'.clusters)
      (h5 : ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
        (τ.restrict S hS).clusters = (τ'.restrict S hS).clusters)
      (A : Finset X) (hA : A ∈ childClusters τ.clusters univ) :
      A ∈ childClusters τ'.clusters univ := by
    have hAU : A ∈ unroot τ.clusters :=
      mem_unroot.2 (Or.inl ⟨(mem_childClusters.1 hA).1, rl_ne_univ_of_mem_childClusters hA⟩)
    refine (hiff τ' (hU ▸ hAU)).2 fun S hS hS5 hAS hAcS => ?_
    rw [← h5 S hS hS5]
    exact (hiff τ hAU).1 hA S hS hS5 hAS hAcS
  ext A
  exact ⟨key σ σ' hU h5 A, key σ' σ hU.symm (fun S hS hS5 => (h5 S hS hS5).symm) A⟩

theorem rl_sameRootedMetricTree_of_clusters_eq (hX : 5 ≤ Fintype.card X) {σ σ' : SpeciesTree X}
    (hcl : σ.clusters = σ'.clusters) (hU : σ.SameUnrootedMetricTree σ')
    (h5 : ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
      (σ.restrict S hS).SameRootedMetricTree (σ'.restrict S hS)) :
    σ.SameRootedMetricTree σ' := by
  have hH := σ.isHierarchy
  refine ⟨hcl, fun A hA hA2 hAu => ?_⟩
  by_cases hAc : Aᶜ ∈ σ.clusters
  · obtain ⟨B₁, hB₁, B₂, hB₂, hne⟩ := one_lt_card.1 (hH.two_le_card_childClusters hA2)
    obtain ⟨a₁, ha₁⟩ := hH.2.2.1 B₁ (mem_childClusters.1 hB₁).1
    obtain ⟨a₂, ha₂⟩ := hH.2.2.1 B₂ (mem_childClusters.1 hB₂).1
    have ha₁A : a₁ ∈ A := (mem_childClusters.1 hB₁).2.1.subset ha₁
    have ha₂A : a₂ ∈ A := (mem_childClusters.1 hB₂).2.1.subset ha₂
    have ha12 : a₁ ≠ a₂ := fun e =>
      disjoint_left.1 (hH.disjoint_of_mem_childClusters hB₁ hB₂ hne) ha₁ (e ▸ ha₂)
    obtain ⟨w', hw'⟩ := rl_compl_nonempty hAu
    obtain ⟨S, hTS, hS5⟩ := rl_exists_five hX (T := {a₁, a₂, w'})
      (card_le_three.trans (by norm_num))
    have ha₁S : a₁ ∈ S := hTS (by simp)
    have ha₂S : a₂ ∈ S := hTS (by simp)
    have hw'S : w' ∈ S := hTS (by simp)
    have hS : S.Nonempty := ⟨a₁, ha₁S⟩
    have hAR : A ∈ childClusters σ.clusters univ :=
      mem_childClusters.2 ⟨hA, ssubset_univ_iff.2 hAu, fun C hC hAC hCu => by
        obtain ⟨x, hxC, hxA⟩ := exists_of_ssubset hAC
        rcases hH.subset_or_subset_of_mem hC hAc hxC (mem_compl.2 hxA) with h | h
        · exact mem_compl.1 (h (hAC.subset ha₁A)) ha₁A
        · exact hCu.ne (eq_univ_of_forall fun y =>
            if hy : y ∈ A then hAC.subset hy else h (mem_compl.2 hy))⟩
    have huniq : ∀ C ∈ σ.clusters, sub S C = sub S A → C = A := by
      intro C hC hCA
      have hmem (x : X) (hx : x ∈ S) : x ∈ C ↔ x ∈ A := mem_iff_of_subtype_eq hCA hx
      have hCu : C ≠ univ := fun e => mem_compl.1 hw' ((hmem w' hw'S).1 (e ▸ mem_univ w'))
      have hAC : A ⊆ C :=
        (hH.subset_or_subset_of_mem hA hC ha₁A ((hmem a₁ ha₁S).2 ha₁A)).elim id fun hCA =>
          hCA.eq_or_ssubset.elim (·.symm.subset) fun hCA => by
            obtain ⟨B, hB, hCB⟩ := hH.exists_mem_childClusters_superset hC hCA
            have h1 : B = B₁ := by_contra fun h =>
              disjoint_left.1 (hH.disjoint_of_mem_childClusters hB hB₁ h)
                (hCB ((hmem a₁ ha₁S).2 ha₁A)) ha₁
            exact absurd ha₂ (disjoint_left.1 (hH.disjoint_of_mem_childClusters (h1 ▸ hB) hB₂ hne)
              (h1 ▸ hCB ((hmem a₂ ha₂S).2 ha₂A)))
      obtain ⟨R, hR, hCR⟩ := hH.exists_mem_childClusters_superset hC (ssubset_univ_iff.2 hCu)
      exact Subset.antisymm (rl_eq_of_mem_childClusters hH hAR hR ha₁A (hCR (hAC ha₁A)) ▸ hCR) hAC
    have h2 : 2 ≤ #(sub S A) :=
      one_lt_card.2 ⟨⟨a₁, ha₁S⟩, mem_subtype.2 ha₁A, ⟨a₂, ha₂S⟩, mem_subtype.2 ha₂A,
        fun h => ha12 (congrArg Subtype.val h)⟩
    have := (h5 S hS hS5).2 _ (subtype_mem_restrictClusters hA ⟨a₁, mem_inter.2 ⟨ha₁A, ha₁S⟩⟩) h2
      (subtype_ne_univ_iff.2 ⟨w', mem_inter.2 ⟨hw', hw'S⟩⟩)
    rwa [SpeciesTree.restrict_length, SpeciesTree.restrict_length,
      σ.restrictLength_subtype_eq hA hAu huniq,
      σ'.restrictLength_subtype_eq (hcl ▸ hA) hAu fun C hC => huniq C (hcl ▸ hC)] at this
  · have hAc2 : 2 ≤ #Aᶜ := by
      by_contra hlt
      obtain ⟨x, hx⟩ := card_eq_one.1 (le_antisymm (by omega) (card_pos.2 (rl_compl_nonempty hAu)))
      exact hAc (hx ▸ σ.singleton_mem x)
    have hunr (τ : SpeciesTree X) (hAτ : A ∈ τ.clusters) (hAcτ : Aᶜ ∉ τ.clusters) :
        τ.unrootedLength A = τ.length A :=
      Finset.sum_eq_single_of_mem A (mem_filter.2 ⟨hAτ, hAu, Or.inl rfl⟩) fun C hC hCA =>
        (mem_filter.1 hC).2.2.elim (fun e => absurd e hCA) (fun e => absurd (e ▸ (mem_filter.1 hC).1) hAcτ)
    rw [← hunr σ hA hAc, ← hunr σ' (hcl ▸ hA) (hcl ▸ hAc)]
    exact hU.2 A (mem_unroot.2 (Or.inl ⟨hA, hAu⟩)) hA2 hAc2


end ADR11
