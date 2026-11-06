module

public import ADR11.Rootings.Proofs
public import ADR11.Trees.Classify
public import ADR11.MSC.Marginal

@[expose] public section

namespace ADR11

open Finset Real

universe u

variable {X : Type u} [Fintype X] [DecidableEq X]

private theorem root_q4 (τ : SpeciesTree (Fin 4)) {H : Finset (Finset (Fin 4))} (hτ : τ.clusters = H)
    (cs : List ℕ) (P₁ P₂ P₃ : List (ℚ × List (ℕ × ℕ)))
    (hwf : wfCsB 4 H cs = true := by decide +kernel)
    (hc : root_certsB 4 (unrootedL 4 cs)
      [(root_Q4code 3, P₁), (root_Q4code 5, P₂), (root_Q4code 9, P₃)] = true := by decide +kernel) :
    τ.unrootedDist id (treeOfClusters {{0, 1}}) = evalPoly τ.length P₁ ∧
    τ.unrootedDist id (treeOfClusters {{0, 2}}) = evalPoly τ.length P₂ ∧
    τ.unrootedDist id (treeOfClusters {{0, 3}}) = evalPoly τ.length P₃ :=
  ⟨root_unrootedDist_eq_evalPoly τ hτ cs hwf hc (t := (root_Q4code 3, P₁))
      List.mem_cons_self (by dsimp; decide +kernel),
    root_unrootedDist_eq_evalPoly τ hτ cs hwf hc (t := (root_Q4code 5, P₂))
      (List.mem_cons_of_mem _ List.mem_cons_self) (by dsimp; decide +kernel),
    root_unrootedDist_eq_evalPoly τ hτ cs hwf hc (t := (root_Q4code 9, P₃))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      (by dsimp; decide +kernel)⟩

private lemma u4_1_single (τ : SpeciesTree (Fin 4)) {H : Finset (Finset (Fin 4))}
    (hc : τ.clusters = H) (cs : List ℕ)
    (hS : H.filter (fun C => C ≠ univ ∧ (C = {0, 1} ∨ C = ({0, 1} : Finset (Fin 4))ᶜ)) =
      {decC 4 cs.headI} := by decide +kernel)
    (hwf : wfCsB 4 H cs = true := by decide +kernel)
    (hcert : root_certsB 4 (unrootedL 4 cs)
      [(root_Q4code 3, [(-2 / 3, [(cs.headI, 1)]), (1, [])]),
       (root_Q4code 5, [(1 / 3, [(cs.headI, 1)])]),
       (root_Q4code 9, [(1 / 3, [(cs.headI, 1)])])] = true := by decide +kernel) :
    τ.unrootedDist id (treeOfClusters {{0, 1}}) = 1 - 2 / 3 * exp (-τ.unrootedLength {0, 1}) ∧
    τ.unrootedDist id (treeOfClusters {{0, 2}}) = 1 / 3 * exp (-τ.unrootedLength {0, 1}) ∧
    τ.unrootedDist id (treeOfClusters {{0, 3}}) = 1 / 3 * exp (-τ.unrootedLength {0, 1}) := by
  obtain ⟨h1, h2, h3⟩ := root_q4 τ hc cs _ _ _ hwf hcert
  have hl : τ.unrootedLength {0, 1} = τ.length (decC 4 cs.headI) := by
    unfold SpeciesTree.unrootedLength; rw [hc, hS, sum_singleton]
  simp only [h1, h2, h3, hl, evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil]
  push_cast
  exact ⟨by ring, by ring, by ring⟩

private lemma u4_0 (τ : SpeciesTree (Fin 4)) {H : Finset (Finset (Fin 4))}
    (hτ : τ.clusters = H) (cs : List ℕ)
    (hwf : wfCsB 4 H cs = true := by decide +kernel)
    (hc : root_certsB 4 (unrootedL 4 cs)
      [(root_Q4code 3, [(1 / 3, [])]), (root_Q4code 5, [(1 / 3, [])]),
       (root_Q4code 9, [(1 / 3, [])])] = true := by decide +kernel) :
    τ.unrootedDist id (treeOfClusters {{0, 1}}) = 1 / 3 ∧
    τ.unrootedDist id (treeOfClusters {{0, 2}}) = 1 / 3 ∧
    τ.unrootedDist id (treeOfClusters {{0, 3}}) = 1 / 3 := by
  obtain ⟨h1, h2, h3⟩ := root_q4 τ hτ cs _ _ _ hwf hc
  simp only [h1, h2, h3, evalPoly_cons, evalPoly_nil, monoVal_nil]
  push_cast
  exact ⟨by ring, by ring, by ring⟩

private theorem four_unrootedLength_pos (σ : SpeciesTree X) {A : Finset X}
    (hA : A ∈ unroot σ.clusters) : 0 < σ.unrootedLength A := by
  refine Finset.sum_pos (fun C hC => σ.length_pos C (mem_filter.1 hC).1 (mem_filter.1 hC).2.1) ?_
  rcases mem_unroot.1 hA with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨A, mem_filter.2 ⟨h1, h2, Or.inl rfl⟩⟩
  · exact ⟨Aᶜ, mem_filter.2 ⟨h1, h2, Or.inr rfl⟩⟩

theorem n4_U4_one (τ : SpeciesTree (Fin 4)) (h : unroot τ.clusters = U4 1) :
    τ.unrootedDist id (treeOfClusters {{0, 1}}) = 1 - 2 / 3 * exp (-τ.unrootedLength {0, 1}) ∧
    τ.unrootedDist id (treeOfClusters {{0, 2}}) = 1 / 3 * exp (-τ.unrootedLength {0, 1}) ∧
    τ.unrootedDist id (treeOfClusters {{0, 3}}) = 1 / 3 * exp (-τ.unrootedLength {0, 1}) := by
  have hm := mem_rootings4 τ 1 (by decide) h
  simp only [rootings4, mem_insert, mem_singleton] at hm
  rcases hm with hc | hc | hc | hc | hc | hc | hc
  · exact u4_1_single τ hc [3, 7]
  · exact u4_1_single τ hc [3, 11]
  · exact u4_1_single τ hc [12, 13]
  · exact u4_1_single τ hc [12, 14]
  · obtain ⟨h1, h2, h3⟩ := root_q4 τ hc [3, 12]
      [(-2 / 3, [(3, 1), (12, 1)]), (1, [])]
      [(1 / 3, [(3, 1), (12, 1)])] [(1 / 3, [(3, 1), (12, 1)])]
    have hl : τ.unrootedLength {0, 1} = τ.length (decC 4 3) + τ.length (decC 4 12) := by
      unfold SpeciesTree.unrootedLength
      rw [show τ.clusters.filter (fun C => C ≠ univ ∧ (C = {0, 1} ∨ C = ({0, 1} : Finset (Fin 4))ᶜ)) =
        {decC 4 3, decC 4 12} by rw [hc]; decide +kernel, sum_pair (by decide +kernel)]
    simp only [h1, h2, h3, hl, evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil,
      neg_add, exp_add]
    push_cast
    exact ⟨by ring, by ring, by ring⟩
  · exact u4_1_single τ hc [3]
  · exact u4_1_single τ hc [12]

private theorem n4_U4_zero (τ : SpeciesTree (Fin 4)) (h : unroot τ.clusters = U4 0) :
    τ.unrootedDist id (treeOfClusters {{0, 1}}) = 1 / 3 ∧
    τ.unrootedDist id (treeOfClusters {{0, 2}}) = 1 / 3 ∧
    τ.unrootedDist id (treeOfClusters {{0, 3}}) = 1 / 3 := by
  have hm := mem_rootings4 τ 0 (by decide) h
  simp only [rootings4, mem_insert, mem_singleton] at hm
  rcases hm with hc | hc | hc | hc | hc
  · exact u4_0 τ hc []
  · exact u4_0 τ hc [7]
  · exact u4_0 τ hc [11]
  · exact u4_0 τ hc [13]
  · exact u4_0 τ hc [14]

private abbrev S4 : Finset (Finset (Finset (Fin 4))) :=
  {treeOfClusters {{0, 1}}, treeOfClusters {{0, 2}}, treeOfClusters {{0, 3}}}

private lemma four_relabel_U4_zero :
    ∀ e ∈ (univ : Finset (Fin 4 ≃ Fin 4)), relabelFamily e (U4 0) = U4 0 := by decide +kernel

private lemma four_relabel_U4_one_mem :
    ∀ e ∈ (univ : Finset (Fin 4 ≃ Fin 4)), relabelFamily e (U4 1) ∈ S4 := by decide +kernel

private lemma four_relabel_S4 :
    ∀ e ∈ (univ : Finset (Fin 4 ≃ Fin 4)), S4.image (relabelFamily e) = S4 := by decide +kernel

private theorem unrootedDist_eq_zero_four (ρ : SpeciesTree (Fin 4)) (T : Finset (Finset (Fin 4)))
    (hT : T ∉ S4) : ρ.unrootedDist id T = 0 := by
  obtain ⟨e, k, hk, he⟩ := exists_equiv_unroot_eq_U4 (Fintype.card_fin 4) ρ
  have hS : ∑ U ∈ S4, ρ.unrootedDist id U = 1 := by
    rw [← four_relabel_S4 e (mem_univ e), sum_image fun x _ y _ h => relabelFamily_injective e h]
    simp_rw [← SpeciesTree.unrootedDist_relabel ρ e.symm, relabelFamily_symm]
    rw [sum_insert (by decide +kernel), sum_insert (by decide +kernel), sum_singleton]
    rcases mem_insert.1 hk with rfl | hk
    · obtain ⟨h1, h2, h3⟩ := n4_U4_zero _ he; linarith
    · obtain ⟨h1, h2, h3⟩ := n4_U4_one _ (mem_singleton.1 hk ▸ he); linarith
  have h0 : ∑ U ∈ univ \ S4, ρ.unrootedDist id U = 0 := by
    have := sum_sdiff (subset_univ S4) (f := ρ.unrootedDist id)
    linarith [unrootedDist_sum ρ id]
  exact (sum_eq_zero_iff_of_nonneg fun U _ => unrootedDist_nonneg ρ id U).1 h0 T
    (mem_sdiff.2 ⟨mem_univ T, hT⟩)

private theorem n4_dichotomy (ρ : SpeciesTree (Fin 4)) :
    unroot ρ.clusters = U4 0 ∨
      (unroot ρ.clusters ∈ S4 ∧ 1 / 3 < ρ.unrootedDist id (unroot ρ.clusters)) := by
  obtain ⟨e, k, hk, he⟩ := exists_equiv_unroot_eq_U4 (Fintype.card_fin 4) ρ
  have hU : unroot ρ.clusters = relabelFamily e (U4 k) := by
    rw [← he, SpeciesTree.relabel_clusters, unroot_relabelFamily]
    exact (relabelFamily_symm e.symm _).symm
  rcases mem_insert.1 hk with rfl | hk
  · exact Or.inl (hU.trans (four_relabel_U4_zero e (mem_univ e)))
  · rw [mem_singleton.1 hk] at he hU
    refine Or.inr ⟨hU ▸ four_relabel_U4_one_mem e (mem_univ e), ?_⟩
    rw [hU, ← SpeciesTree.unrootedDist_relabel ρ e.symm, relabelFamily_symm]
    change 1 / 3 < (ρ.relabel e.symm).unrootedDist id (treeOfClusters {{0, 1}})
    rw [(n4_U4_one _ he).1]
    have : exp (-(ρ.relabel e.symm).unrootedLength {0, 1}) < 1 :=
      exp_lt_one_iff.2 (neg_lt_zero.2 (four_unrootedLength_pos _ (by rw [he]; decide)))
    linarith

theorem unrootedDist_eq_iff_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' := by
  obtain ⟨e, k, hk, he⟩ := exists_equiv_unroot_eq_U4 hX σ
  rw [← SpeciesTree.unrootedDist_relabel_eq_iff σ σ' e.symm,
    ← SpeciesTree.sameUnrootedMetricTree_relabel_iff σ σ' e.symm]
  set τ := σ.relabel e.symm
  set τ' := σ'.relabel e.symm
  constructor
  · intro h
    rcases mem_insert.1 hk with rfl | hk
    · obtain ⟨h1, h2, h3⟩ := n4_U4_zero τ he
      rcases n4_dichotomy τ' with he' | ⟨hm, hgt⟩
      · refine ⟨he.trans he'.symm, fun A hA hA1 hA2 => ?_⟩
        exfalso; revert A; rw [he]; decide
      · rw [← h] at hgt
        simp only [mem_insert, mem_singleton] at hm
        rcases hm with hU | hU | hU <;> linarith [hU ▸ hgt]
    · rw [mem_singleton.1 hk] at he
      obtain ⟨h1, h2, h3⟩ := n4_U4_one τ he
      have hlt : exp (-τ.unrootedLength {0, 1}) < 1 :=
        exp_lt_one_iff.2 (neg_lt_zero.2 (four_unrootedLength_pos τ (by rw [he]; decide)))
      rcases n4_dichotomy τ' with he' | ⟨hm, hgt⟩
      · have h1' := (n4_U4_zero τ' he').1
        rw [h] at h1; linarith
      · rw [← h] at hgt
        simp only [mem_insert, mem_singleton] at hm
        have he' : unroot τ'.clusters = U4 1 := by
          rcases hm with hU | hU | hU
          · exact hU
          all_goals linarith [hU ▸ hgt]
        have hlen01 : τ.unrootedLength {0, 1} = τ'.unrootedLength {0, 1} := by
          have h1' := (n4_U4_one τ' he').1
          rw [h, h1'] at h1
          have : exp (-τ.unrootedLength {0, 1}) = exp (-τ'.unrootedLength {0, 1}) := by linarith
          exact neg_inj.1 (exp_eq_exp.1 this)
        refine ⟨he.trans he'.symm, fun A hA hA1 hA2 => ?_⟩
        have hA01 : A = {0, 1} ∨ A = ({0, 1} : Finset (Fin 4))ᶜ := by
          revert A hA1 hA2; rw [he]; decide
        rcases hA01 with rfl | rfl
        · exact hlen01
        · rw [SpeciesTree.unrootedLength_compl, SpeciesTree.unrootedLength_compl, hlen01]
  · rintro ⟨hU, hL⟩
    have he' : unroot τ'.clusters = U4 k := hU ▸ he
    have ⟨e1, e2, e3⟩ : τ.unrootedDist id (treeOfClusters {{0, 1}}) =
          τ'.unrootedDist id (treeOfClusters {{0, 1}}) ∧
        τ.unrootedDist id (treeOfClusters {{0, 2}}) =
          τ'.unrootedDist id (treeOfClusters {{0, 2}}) ∧
        τ.unrootedDist id (treeOfClusters {{0, 3}}) =
          τ'.unrootedDist id (treeOfClusters {{0, 3}}) := by
      rcases mem_insert.1 hk with rfl | hk
      · obtain ⟨h1, h2, h3⟩ := n4_U4_zero τ he
        obtain ⟨h1', h2', h3'⟩ := n4_U4_zero τ' he'
        exact ⟨h1.trans h1'.symm, h2.trans h2'.symm, h3.trans h3'.symm⟩
      · rw [mem_singleton.1 hk] at he he'
        have hlen := hL {0, 1} (by rw [he]; decide) (by decide) (by decide)
        obtain ⟨h1, h2, h3⟩ := n4_U4_one τ he
        obtain ⟨h1', h2', h3'⟩ := n4_U4_one τ' he'
        rw [hlen] at h1 h2 h3
        exact ⟨h1.trans h1'.symm, h2.trans h2'.symm, h3.trans h3'.symm⟩
    funext T
    by_cases hT : T ∈ S4
    · simp only [mem_insert, mem_singleton] at hT
      rcases hT with hT | hT | hT
      · exact hT ▸ e1
      · exact hT ▸ e2
      · exact hT ▸ e3
    · rw [unrootedDist_eq_zero_four τ T hT, unrootedDist_eq_zero_four τ' T hT]

theorem rl_compl_nonempty {A : Finset X} (hAu : A ≠ univ) : Aᶜ.Nonempty := by
  obtain ⟨x, hx⟩ := not_forall.1 fun h => hAu (eq_univ_iff_forall.2 h)
  exact ⟨x, mem_compl.2 hx⟩

theorem steel_nonempty_of_mem_unroot (σ : SpeciesTree X) {A : Finset X}
    (h : A ∈ unroot σ.clusters) : A.Nonempty := by
  rcases mem_unroot.1 h with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact σ.nonempty_of_mem A h1
  · rw [nonempty_iff_ne_empty]; rintro rfl; exact h2 compl_empty

private theorem steel_laminar_avoid (σ : SpeciesTree X) {b₀ : X} {C D : Finset X}
    (hC : C ∈ unroot σ.clusters) (hD : D ∈ unroot σ.clusters) (hC₀ : b₀ ∉ C)
    (hD₀ : b₀ ∉ D) : C ⊆ D ∨ D ⊆ C ∨ Disjoint C D := by
  rcases mem_unroot.1 hC with ⟨hC1, -⟩ | ⟨hC1, -⟩ <;>
    rcases mem_unroot.1 hD with ⟨hD1, -⟩ | ⟨hD1, -⟩
  · exact σ.laminar C hC1 D hD1
  · rcases σ.laminar C hC1 Dᶜ hD1 with h | h | h
    · exact Or.inr (Or.inr (subset_compl_iff_disjoint_right.1 h))
    · exact absurd (h (mem_compl.2 hD₀)) hC₀
    · exact Or.inl (disjoint_compl_right_iff.1 h)
  · rcases σ.laminar Cᶜ hC1 D hD1 with h | h | h
    · exact absurd (h (mem_compl.2 hC₀)) hD₀
    · exact Or.inr (Or.inr (subset_compl_iff_disjoint_right.1 h).symm)
    · exact Or.inr (Or.inl (disjoint_compl_left_iff.1 h))
  · rcases σ.laminar Cᶜ hC1 Dᶜ hD1 with h | h | h
    · exact Or.inr (Or.inl (compl_subset_compl.1 h))
    · exact Or.inl (compl_subset_compl.1 h)
    · exact absurd (mem_compl.2 hD₀) (disjoint_left.1 h (mem_compl.2 hC₀))

theorem mem_unroot_iff_quartets (σ : SpeciesTree X) {A : Finset X} (hA : 2 ≤ #A)
    (hA' : 2 ≤ #Aᶜ) :
    A ∈ unroot σ.clusters ↔
      ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ Aᶜ, ∀ b' ∈ Aᶜ, a ≠ a' → b ≠ b' →
        ∃ C ∈ unroot σ.clusters, a ∈ C ∧ a' ∈ C ∧ b ∉ C ∧ b' ∉ C := by
  refine ⟨fun h a ha a' ha' b hb b' hb' _ _ =>
    ⟨A, h, ha, ha', mem_compl.1 hb, mem_compl.1 hb'⟩, fun hq => ?_⟩
  obtain ⟨b₀, hb₀⟩ : Aᶜ.Nonempty := card_pos.1 (by omega)
  have hb₀A : b₀ ∉ A := mem_compl.1 hb₀
  obtain ⟨b₁, hb₁, hb₁₀⟩ := exists_mem_ne (show 1 < #Aᶜ by omega) b₀
  have hAne : A.Nonempty := card_pos.1 (by omega)
  set F := (unroot σ.clusters).filter fun C => b₀ ∉ C
  set H := insert univ (insert {b₀} F)
  have hsing : ∀ x : X, {x} ∈ H := fun x => by
    by_cases hx : x = b₀
    · exact hx ▸ mem_insert_of_mem (mem_insert_self _ _)
    · by_cases hu : ({x} : Finset X) = univ
      · exact hu ▸ mem_insert_self _ _
      · exact mem_insert_of_mem (mem_insert_of_mem (mem_filter.2
          ⟨mem_unroot.2 (Or.inl ⟨σ.singleton_mem x, hu⟩), by simp [Ne.symm hx]⟩))
  have hH : IsHierarchy H :=
    ⟨mem_insert_self _ _, hsing,
      by rintro C hC
         rcases mem_insert.1 hC with rfl | hC; · exact ⟨b₀, mem_univ _⟩
         rcases mem_insert.1 hC with rfl | hC; · exact singleton_nonempty _
         exact steel_nonempty_of_mem_unroot σ (mem_filter.1 hC).1,
      by intro C hC D hD
         rcases mem_insert.1 hC with rfl | hC; · exact Or.inr (Or.inl (subset_univ _))
         rcases mem_insert.1 hD with rfl | hD; · exact Or.inl (subset_univ _)
         rcases mem_insert.1 hC with rfl | hC <;> rcases mem_insert.1 hD with rfl | hD
         · exact Or.inl (subset_refl _)
         · exact Or.inr (Or.inr (disjoint_singleton_left.2 (mem_filter.1 hD).2))
         · exact Or.inr (Or.inr (disjoint_singleton_right.2 (mem_filter.1 hC).2))
         · exact steel_laminar_avoid σ (mem_filter.1 hC).1 (mem_filter.1 hD).1 (mem_filter.1 hC).2
             (mem_filter.1 hD).2⟩
  have key : A ∈ H := by
    refine hH.mem_of_triples hAne fun a ha a' ha' b hb => ?_
    by_cases haa : a = a'
    · subst haa
      exact ⟨{a}, hsing a, mem_singleton_self a, mem_singleton_self a,
        fun e => hb (mem_singleton.1 e ▸ ha)⟩
    · by_cases hbb : b = b₀
      · subst hbb
        obtain ⟨C, hC, h1, h2, -, h4⟩ := hq a ha a' ha' b₁ hb₁ b hb₀ haa hb₁₀
        exact ⟨C, mem_insert_of_mem (mem_insert_of_mem (mem_filter.2 ⟨hC, h4⟩)), h1, h2, h4⟩
      · obtain ⟨C, hC, h1, h2, h3, h4⟩ := hq a ha a' ha' b (mem_compl.2 hb) b₀ hb₀ haa hbb
        exact ⟨C, mem_insert_of_mem (mem_insert_of_mem (mem_filter.2 ⟨hC, h4⟩)), h1, h2, h3⟩
  rcases mem_insert.1 key with h | h; · exact absurd (h ▸ mem_univ b₀) hb₀A
  rcases mem_insert.1 h with h | h; · exact absurd (h ▸ mem_singleton_self b₀) hb₀A
  exact (mem_filter.1 h).1

private theorem steel_distinguishing_of_mem_clusters (σ : SpeciesTree X) {A : Finset X}
    (hA : A ∈ σ.clusters) (hAu : A ≠ univ) (hA₁ : 2 ≤ #A) (hA₂ : 2 ≤ #Aᶜ) :
    ∃ a ∈ A, ∃ a' ∈ A, ∃ b ∈ Aᶜ, ∃ b' ∈ Aᶜ, a ≠ a' ∧ b ≠ b' ∧
      ∀ C ∈ unroot σ.clusters, a ∈ C → a' ∈ C → b ∉ C → b' ∉ C → C = A := by
  obtain ⟨z, hz⟩ : A.Nonempty := card_pos.1 (by omega)
  obtain ⟨a, ha, a', ha', haa, hpair⟩ := σ.isHierarchy.exists_pair_of_two_le_card hA₁
  have hup : ∀ C ∈ σ.clusters, a ∈ C → a' ∈ C → A ⊆ C := fun C hC h1 h2 => by
    rcases σ.laminar C hC A hA with h | h | h
    · exact (by_contra fun hne => hpair C hC h1 h2 (Finset.ssubset_iff_subset_ne.2 ⟨h, hne⟩) : C = A) ▸ subset_rfl
    · exact h
    · exact absurd ha (disjoint_left.1 h h1)
  obtain ⟨P, hP, hPmin⟩ := exists_min_image (σ.clusters.filter fun C => A ⊂ C) card
    ⟨univ, mem_filter.2 ⟨σ.univ_mem, ssubset_univ_iff.2 hAu⟩⟩
  obtain ⟨hPc, hAP⟩ := mem_filter.1 hP
  have hPle : ∀ C ∈ σ.clusters, A ⊂ C → P ⊆ C := fun C hC hAC => by
    have hle := hPmin C (mem_filter.2 ⟨hC, hAC⟩)
    rcases σ.laminar C hC P hPc with h | h | h
    · exact (eq_of_subset_of_card_le h hle).symm.subset
    · exact h
    · exact absurd (hAP.1 hz) (disjoint_left.1 h (hAC.1 hz))
  obtain ⟨b, hb, b', hb', hbb, hP1, hP2⟩ : ∃ b ∈ Aᶜ, ∃ b' ∈ Aᶜ, b ≠ b' ∧
      (∀ C ∈ σ.clusters, A ⊂ C → b ∈ C ∨ b' ∈ C) ∧
      (∀ D ∈ σ.clusters, b ∈ D → b' ∈ D → ¬ D ⊂ Aᶜ) := by
    by_cases hPu : P = univ
    · obtain ⟨b, hb, b', hb', hbb, h⟩ := σ.isHierarchy.exists_pair_of_two_le_card hA₂
      exact ⟨b, hb, b', hb', hbb, fun C hC hAC => Or.inl (hPle C hC hAC (hPu ▸ mem_univ b)), h⟩
    · obtain ⟨b, hbP, hbA⟩ := exists_of_ssubset hAP
      obtain ⟨b', hb'⟩ := rl_compl_nonempty hPu
      rw [mem_compl] at hb'
      refine ⟨b, mem_compl.2 hbA, b', mem_compl.2 (fun h => hb' (hAP.1 h)),
        fun e => hb' (e ▸ hbP), fun C hC hAC => Or.inl (hPle C hC hAC hbP),
        fun D hD hbD hb'D hDA => ?_⟩
      rcases σ.laminar D hD P hPc with h | h | h
      · exact hb' (h hb'D)
      · exact mem_compl.1 (hDA.1 (h (hAP.1 hz))) hz
      · exact disjoint_left.1 h hbD hbP
  refine ⟨a, ha, a', ha', b, hb, b', hb', haa, hbb, fun C hC haC ha'C hbC hb'C => ?_⟩
  rcases mem_unroot.1 hC with ⟨hC1, -⟩ | ⟨hC1, -⟩
  · have hAC := hup C hC1 haC ha'C
    by_contra hne
    rcases hP1 C hC1 (Finset.ssubset_iff_subset_ne.2 ⟨hAC, Ne.symm hne⟩) with h | h
    · exact hbC h
    · exact hb'C h
  · have hbD : b ∈ Cᶜ := mem_compl.2 hbC
    have hb'D : b' ∈ Cᶜ := mem_compl.2 hb'C
    have hDA : Cᶜ ⊆ Aᶜ := by
      rcases σ.laminar Cᶜ hC1 A hA with h | h | h
      · exact absurd (h hbD) (mem_compl.1 hb)
      · exact absurd haC (mem_compl.1 (h ha))
      · exact subset_compl_iff_disjoint_right.2 h
    exact compl_injective (by_contra fun hne =>
      hP2 Cᶜ hC1 hbD hb'D (Finset.ssubset_iff_subset_ne.2 ⟨hDA, hne⟩))

theorem exists_distinguishing_quartet (σ : SpeciesTree X) {A : Finset X}
    (hA : A ∈ unroot σ.clusters) (hA₁ : 2 ≤ #A) (hA₂ : 2 ≤ #Aᶜ) :
    ∃ a ∈ A, ∃ a' ∈ A, ∃ b ∈ Aᶜ, ∃ b' ∈ Aᶜ, a ≠ a' ∧ b ≠ b' ∧
      ∀ C ∈ unroot σ.clusters, a ∈ C → a' ∈ C → b ∉ C → b' ∉ C → C = A := by
  rcases mem_unroot.1 hA with ⟨hA1, hA2⟩ | ⟨hA1, hA2⟩
  · exact steel_distinguishing_of_mem_clusters σ hA1 hA2 hA₁ hA₂
  · obtain ⟨a, ha, a', ha', b, hb, b', hb', haa, hbb, h⟩ :=
      steel_distinguishing_of_mem_clusters σ hA1 hA2 hA₂ (by rwa [compl_compl])
    rw [compl_compl] at hb hb'
    refine ⟨b, hb, b', hb', a, ha, a', ha', hbb, haa, fun C hC hbC hb'C haC ha'C => ?_⟩
    exact compl_injective (h Cᶜ (compl_mem_unroot.2 hC) (mem_compl.2 haC) (mem_compl.2 ha'C)
      (fun h' => mem_compl.1 h' hbC) (fun h' => mem_compl.1 h' hb'C))

theorem unrootedDist_restrict_eq {σ σ' : SpeciesTree X}
    (h : σ.unrootedDist id = σ'.unrootedDist id) (S : Finset X) (hS : S.Nonempty) :
    (σ.restrict S hS).unrootedDist id = (σ'.restrict S hS).unrootedDist id := by
  have key : ∀ τ : SpeciesTree X, ∀ T', (τ.restrict S hS).unrootedDist id T' =
      ∑ T, if restrictUnrooted (Function.Embedding.subtype (· ∈ S)) T = T' then
        τ.unrootedDist id T else 0 := fun τ T' => by
    rw [← τ.unrootedDist_comp_embedding id (Function.Embedding.subtype (· ∈ S)) T']
    unfold SpeciesTree.unrootedDist
    simp_rw [τ.rootedDist_restrict S hS id]; rfl
  funext T'; rw [key, key, h]

omit [Fintype X] in
theorem rl_mem_iff_of_subtype_eq {S A C : Finset X}
    (h : C.subtype (· ∈ S) = A.subtype (· ∈ S)) (x : X) (hx : x ∈ S) : x ∈ C ↔ x ∈ A := by
  have h1 : (⟨x, hx⟩ : S) ∈ C.subtype (· ∈ S) ↔ (⟨x, hx⟩ : S) ∈ A.subtype (· ∈ S) := by rw [h]
  simpa only [mem_subtype] using h1

omit [Fintype X] in
private theorem quart_card_quartet {A : Finset X} {a a' b b' : X}
    (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∉ A) (hb' : b' ∉ A) (haa : a ≠ a') (hbb : b ≠ b') :
    #({a, a', b, b'} : Finset X) = 4 := by
  rw [card_insert_of_notMem (by simp only [mem_insert, mem_singleton]; rintro (rfl | rfl | rfl); exacts [haa rfl, hb ha, hb' ha]),
    card_insert_of_notMem (by simp only [mem_insert, mem_singleton]; rintro (rfl | rfl); exacts [hb ha', hb' ha']),
    card_pair hbb]

private theorem quart_unroot_subset (σ σ' : SpeciesTree X)
    (h : ∀ Q : Finset X, ∀ hQ : Q.Nonempty, #Q = 4 →
      unroot (σ.restrict Q hQ).clusters = unroot (σ'.restrict Q hQ).clusters) :
    unroot σ.clusters ⊆ unroot σ'.clusters := by
  intro A hA
  have hAne := steel_nonempty_of_mem_unroot σ hA
  have hAcne := steel_nonempty_of_mem_unroot σ (compl_mem_unroot.2 hA)
  by_cases h1 : #A ≤ 1
  · obtain ⟨x, rfl⟩ := card_eq_one.1 (le_antisymm h1 (card_pos.2 hAne))
    exact mem_unroot.2 (Or.inl ⟨σ'.singleton_mem x, fun hu =>
      hAcne.ne_empty (by rw [hu, compl_univ])⟩)
  by_cases h2 : #Aᶜ ≤ 1
  · obtain ⟨x, hx⟩ := card_eq_one.1 (le_antisymm h2 (card_pos.2 hAcne))
    exact mem_unroot.2 (Or.inr ⟨hx ▸ σ'.singleton_mem x, fun hu =>
      hAne.ne_empty (by rw [← compl_compl A, hu, compl_univ])⟩)
  rw [mem_unroot_iff_quartets σ' (by omega) (by omega)]
  intro a ha a' ha' b hb b' hb' haa hbb
  rw [mem_compl] at hb hb'
  set Q : Finset X := {a, a', b, b'}
  have hQ : Q.Nonempty := insert_nonempty _ _
  have haQ : a ∈ Q := by simp [Q]
  have ha'Q : a' ∈ Q := by simp [Q]
  have hbQ : b ∈ Q := by simp [Q]
  have hb'Q : b' ∈ Q := by simp [Q]
  have hU := h Q hQ (quart_card_quartet ha ha' hb hb' haa hbb)
  obtain ⟨C, hC, -, -, hCA⟩ := (σ'.mem_unroot_restrict hQ).1 (hU ▸ (σ.mem_unroot_restrict hQ).2
    ⟨A, hA, ⟨a, mem_inter.2 ⟨ha, haQ⟩⟩, ⟨b, mem_inter.2 ⟨mem_compl.2 hb, hbQ⟩⟩, rfl⟩)
  have key := rl_mem_iff_of_subtype_eq hCA
  exact ⟨C, hC, (key a haQ).2 ha, (key a' ha'Q).2 ha',
    fun h => hb ((key b hbQ).1 h), fun h => hb' ((key b' hb'Q).1 h)⟩

theorem sameUnrootedMetricTree_of_unrootedDist_eq (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameUnrootedMetricTree σ' := by
  have hR : ∀ Q : Finset X, ∀ hQ : Q.Nonempty, #Q = 4 →
      (σ.restrict Q hQ).SameUnrootedMetricTree (σ'.restrict Q hQ) := fun Q hQ hQ4 =>
    (unrootedDist_eq_iff_four (by simpa using hQ4) _ _).1 (unrootedDist_restrict_eq h Q hQ)
  have hU : unroot σ.clusters = unroot σ'.clusters :=
    Subset.antisymm (quart_unroot_subset σ σ' fun Q hQ hQ4 => (hR Q hQ hQ4).1)
      (quart_unroot_subset σ' σ fun Q hQ hQ4 => (hR Q hQ hQ4).1.symm)
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
  obtain ⟨_, hLQ⟩ := hR Q hQ (quart_card_quartet ha ha' hb hb' haa hbb)
  have hC₀ := (σ.mem_unroot_restrict hQ).2
    ⟨A, hA, ⟨a, mem_inter.2 ⟨ha, haQ⟩⟩, ⟨b, mem_inter.2 ⟨mem_compl.2 hb, hbQ⟩⟩, rfl⟩
  have hC₀₁ : 2 ≤ #(A.subtype (· ∈ Q)) :=
    one_lt_card.2 ⟨⟨a, haQ⟩, mem_subtype.2 ha, ⟨a', ha'Q⟩, mem_subtype.2 ha',
      fun h => haa (congrArg Subtype.val h)⟩
  have hC₀₂ : 2 ≤ #(A.subtype (· ∈ Q))ᶜ :=
    one_lt_card.2 ⟨⟨b, hbQ⟩, by simp [hb], ⟨b', hb'Q⟩, by simp [hb'],
      fun h => hbb (congrArg Subtype.val h)⟩
  have hlen : ∀ τ : SpeciesTree X,
      (∀ C ∈ unroot τ.clusters, a ∈ C → a' ∈ C → b ∉ C → b' ∉ C → C = A) →
      (τ.restrict Q hQ).unrootedLength (A.subtype (· ∈ Q)) = τ.unrootedLength A := by
    intro τ huniqτ
    rw [τ.restrict_unrootedLength Q hQ _ (card_pos.1 (by omega)) (card_pos.1 (by omega))]
    unfold SpeciesTree.unrootedLength
    refine sum_congr (filter_congr fun B hB => and_congr_right fun hBu => ?_) fun _ _ => rfl
    have hBU : B ∈ unroot τ.clusters := mem_unroot.2 (Or.inl ⟨hB, hBu⟩)
    constructor
    · rintro (h1 | h1)
      · have k := rl_mem_iff_of_subtype_eq h1
        exact Or.inl (huniqτ B hBU ((k a haQ).2 ha) ((k a' ha'Q).2 ha')
          (mt (k b hbQ).1 hb) (mt (k b' hb'Q).1 hb'))
      · have h2 : Bᶜ.subtype (· ∈ Q) = A.subtype (· ∈ Q) := by rw [subtype_compl, h1, compl_compl]
        have k := rl_mem_iff_of_subtype_eq h2
        refine Or.inr (by rw [← compl_compl B, huniqτ Bᶜ (compl_mem_unroot.2 hBU)
          ((k a haQ).2 ha) ((k a' ha'Q).2 ha') (mt (k b hbQ).1 hb) (mt (k b' hb'Q).1 hb')])
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (subtype_compl A)
  rw [← hlen σ huniq, ← hlen σ' (hU ▸ huniq)]
  exact hLQ _ hC₀ hC₀₁ hC₀₂

theorem rl_mem_childClusters_of_compl_mem {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A : Finset X} (hA : A ∈ H) (hAc : Aᶜ ∈ H) : A ∈ childClusters H univ := by
  obtain ⟨x, hx⟩ := hH.2.2.1 Aᶜ hAc
  obtain ⟨a, ha⟩ := hH.2.2.1 A hA
  refine mem_childClusters.2 ⟨hA, ssubset_univ_iff.2 fun e => mem_compl.1 hx (e ▸ mem_univ x),
    fun C hC hAC hCu => ?_⟩
  obtain ⟨y, hyC, hyA⟩ := exists_of_ssubset hAC
  rcases hH.2.2.2 C hC Aᶜ hAc with h | h | h
  · exact mem_compl.1 (h (hAC.subset ha)) ha
  · exact not_subset_of_ssubset hCu (union_compl A ▸ union_subset hAC.subset h)
  · exact disjoint_left.1 h hyC (mem_compl.2 hyA)

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
  have hiff : ∀ {G : Finset (Finset X)} (hG : IsHierarchy G) (C : Finset X),
      C ∈ G ↔ C = univ ∨ (C ∈ unroot G ∧ ∃ R ∈ childClusters G univ, C ⊆ R) := fun hG C => by
    constructor
    · intro hC
      by_cases hCu : C = univ
      · exact Or.inl hCu
      · exact Or.inr ⟨mem_unroot.2 (Or.inl ⟨hC, hCu⟩),
          hG.exists_mem_childClusters_superset hC (ssubset_univ_iff.2 hCu)⟩
    · rintro (rfl | ⟨hC, R, hR, hCR⟩)
      · exact hG.1
      · rcases mem_unroot.1 hC with ⟨h, -⟩ | ⟨h, hu⟩
        · exact h
        · have hRG := (mem_childClusters.1 hR).1
          have hRu := rl_ne_univ_of_mem_childClusters hR
          rcases hG.2.2.2 _ h R hRG with h' | h' | h'
          · exact absurd (univ_subset_iff.1 (by rw [← union_compl C]; exact union_subset hCR h')) hRu
          · exact absurd (univ_subset_iff.1 (by rw [← union_compl C]; exact union_subset (hCR.trans h') subset_rfl)) hu
          · exact compl_inj_iff.1 (Subset.antisymm (subset_compl_iff_disjoint_right.2 h')
              (compl_subset_compl.2 hCR)) ▸ hRG
  ext C; rw [hiff hH, hiff hH', hU, hR]

theorem rl_mem_childClusters_restrict_iff (σ : SpeciesTree X) {S : Finset X} (hS : S.Nonempty)
    (hmrca : ∀ R ∈ childClusters σ.clusters univ, ¬ S ⊆ R) {C : Finset S} :
    C ∈ childClusters (σ.restrict S hS).clusters univ ↔
      ∃ R ∈ childClusters σ.clusters univ, (R ∩ S).Nonempty ∧ R.subtype (· ∈ S) = C := by
  have hH := σ.isHierarchy
  have htr : ∀ R ∈ childClusters σ.clusters univ, (R ∩ S).Nonempty →
      R.subtype (· ∈ S) ∈ (σ.restrict S hS).clusters ∧ R.subtype (· ∈ S) ⊂ univ := by
    intro R hR hRS
    refine ⟨subtype_mem_restrictClusters (mem_childClusters.1 hR).1 hRS,
      ssubset_univ_iff.2 (subtype_ne_univ_iff.2 ?_)⟩
    obtain ⟨y, hyS, hyR⟩ := not_subset.1 (hmrca R hR)
    exact ⟨y, mem_inter.2 ⟨mem_compl.2 hyR, hyS⟩⟩
  have hsup : ∀ B ∈ σ.clusters, B ≠ univ → ∃ R ∈ childClusters σ.clusters univ, B ⊆ R :=
    fun B hB hBu => hH.exists_mem_childClusters_superset hB (ssubset_univ_iff.2 hBu)
  constructor
  · intro hC
    obtain ⟨hCcl, hCu, hmax⟩ := mem_childClusters.1 hC
    obtain ⟨B, hB, hBS, rfl⟩ := mem_restrictClusters.1 hCcl
    have hBu : B ≠ univ := fun e => (ssubset_univ_iff.1 hCu) (e ▸ subtype_univ _)
    obtain ⟨R, hR, hBR⟩ := hsup B hB hBu
    have hRS : (R ∩ S).Nonempty := hBS.mono (inter_subset_inter_right hBR)
    refine ⟨R, hR, hRS, ?_⟩
    obtain ⟨hRcl, hRu⟩ := htr R hR hRS
    rcases (subtype_mono hBR : B.subtype (· ∈ S) ⊆ R.subtype (· ∈ S)).eq_or_ssubset with h | h
    · exact h.symm
    · exact absurd hRu (hmax _ hRcl h)
  · rintro ⟨R, hR, hRS, rfl⟩
    obtain ⟨hRcl, hRu⟩ := htr R hR hRS
    refine mem_childClusters.2 ⟨hRcl, hRu, fun D hD hRD hDu => ?_⟩
    obtain ⟨B, hB, -, rfl⟩ := mem_restrictClusters.1 hD
    have hBu : B ≠ univ := fun e => (ssubset_univ_iff.1 hDu) (e ▸ subtype_univ _)
    obtain ⟨R', hR', hBR'⟩ := hsup B hB hBu
    obtain ⟨y, hy⟩ := hRS
    have hyB : y ∈ B := mem_subtype.1
      (hRD.subset (mem_subtype.2 (mem_inter.1 hy).1 : (⟨y, (mem_inter.1 hy).2⟩ : S) ∈ _))
    have := rl_eq_of_mem_childClusters hH hR hR' (mem_inter.1 hy).1 (hBR' hyB)
    subst this
    exact not_subset_of_ssubset hRD (subtype_mono hBR')

omit [DecidableEq X] in
theorem rl_exists_five (hX : 5 ≤ Fintype.card X) {T : Finset X} (hT : #T ≤ 5) :
    ∃ S, T ⊆ S ∧ #S = 5 := by
  obtain ⟨S, hTS, -, hS⟩ := exists_subsuperset_card_eq (subset_univ T) hT (by rwa [card_univ])
  exact ⟨S, hTS, hS⟩

theorem rl_sameRootedMetricTree_of_clusters_eq (hX : 5 ≤ Fintype.card X) {σ σ' : SpeciesTree X}
    (hcl : σ.clusters = σ'.clusters) (hU : σ.SameUnrootedMetricTree σ')
    (h5 : ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
      (σ.restrict S hS).SameRootedMetricTree (σ'.restrict S hS)) :
    σ.SameRootedMetricTree σ' := by
  refine ⟨hcl, fun A hA hA2 hAu => ?_⟩
  by_cases hAc : Aᶜ ∈ σ.clusters
  · have hH := σ.isHierarchy
    have hAR := rl_mem_childClusters_of_compl_mem hH hA hAc
    obtain ⟨a₁, ha₁, a₂, ha₂, ha12, hpair⟩ := hH.exists_pair_of_two_le_card hA2
    obtain ⟨w', hw'⟩ := σ.nonempty_of_mem Aᶜ hAc
    obtain ⟨S, hTS, hS5⟩ := rl_exists_five hX (T := {a₁, a₂, w'}) (card_le_three.trans (by norm_num))
    have ha₁S : a₁ ∈ S := hTS (by simp)
    have ha₂S : a₂ ∈ S := hTS (by simp)
    have hw'S : w' ∈ S := hTS (by simp)
    have hS : S.Nonempty := ⟨a₁, ha₁S⟩
    have huniq : ∀ C ∈ σ.clusters, C.subtype (· ∈ S) = A.subtype (· ∈ S) → C = A := by
      intro C hC hCA
      have hmem := rl_mem_iff_of_subtype_eq hCA
      have hCu : C ≠ univ := fun e =>
        mem_compl.1 hw' ((hmem w' hw'S).1 (e ▸ mem_univ w'))
      have ha₁C : a₁ ∈ C := (hmem a₁ ha₁S).2 ha₁
      have ha₂C : a₂ ∈ C := (hmem a₂ ha₂S).2 ha₂
      have hAC : A ⊆ C := by
        rcases hH.subset_or_subset_of_mem hC hA ha₁C ha₁ with h | h
        · exact (by_contra fun hne => hpair C hC ha₁C ha₂C (h.ssubset_of_ne hne) : C = A).symm.subset
        · exact h
      obtain ⟨R, hR, hCR⟩ := hH.exists_mem_childClusters_superset hC (ssubset_univ_iff.2 hCu)
      exact Subset.antisymm (rl_eq_of_mem_childClusters hH hAR hR ha₁ (hCR ha₁C) ▸ hCR) hAC
    have h2 : 2 ≤ #(A.subtype (· ∈ S)) :=
      one_lt_card.2 ⟨⟨a₁, ha₁S⟩, mem_subtype.2 ha₁, ⟨a₂, ha₂S⟩, mem_subtype.2 ha₂,
        fun h => ha12 (congrArg Subtype.val h)⟩
    have := (h5 S hS hS5).2 _ (subtype_mem_restrictClusters hA ⟨a₁, mem_inter.2 ⟨ha₁, ha₁S⟩⟩)
      h2 (subtype_ne_univ_iff.2 ⟨w', mem_inter.2 ⟨hw', hw'S⟩⟩)
    rwa [SpeciesTree.restrict_length, SpeciesTree.restrict_length,
      σ.restrictLength_subtype_eq hA hAu huniq,
      σ'.restrictLength_subtype_eq (hcl ▸ hA) hAu fun C hC => huniq C (hcl ▸ hC)] at this
  · have hAc2 : 2 ≤ #Aᶜ := by
      by_contra hlt
      obtain ⟨x, hx⟩ := card_eq_one.1
        (le_antisymm (by omega) (card_pos.2 (rl_compl_nonempty hAu)))
      exact hAc (hx ▸ σ.singleton_mem x)
    have hul : ∀ τ : SpeciesTree X, A ∈ τ.clusters → Aᶜ ∉ τ.clusters →
        τ.unrootedLength A = τ.length A := fun τ hAt hAct => by
      unfold SpeciesTree.unrootedLength
      rw [Finset.sum_eq_single_of_mem A (mem_filter.2 ⟨hAt, hAu, Or.inl rfl⟩)]
      intro C hC hCA
      obtain ⟨hC1, -, rfl | rfl⟩ := mem_filter.1 hC
      · exact absurd rfl hCA
      · exact absurd hC1 hAct
    rw [← hul σ hA hAc, ← hul σ' (hcl ▸ hA) (hcl ▸ hAc)]
    exact hU.2 A (mem_unroot.2 (Or.inl ⟨hA, hAu⟩)) hA2 hAc2

theorem rl_nb_exists_five_not_mem_childClusters (hX : 5 ≤ Fintype.card X) (σ : SpeciesTree X)
    {A : Finset X} (hA : A ∈ unroot σ.clusters) (hAR : A ∉ childClusters σ.clusters univ) :
    ∃ S : Finset X, ∃ hS : S.Nonempty, #S = 5 ∧ (A ∩ S).Nonempty ∧ (Aᶜ ∩ S).Nonempty ∧
      A.subtype (· ∈ S) ∉ childClusters (σ.restrict S hS).clusters univ := by
  have hH := σ.isHierarchy
  have hAne := steel_nonempty_of_mem_unroot σ hA
  have hAcne := steel_nonempty_of_mem_unroot σ (compl_mem_unroot.2 hA)
  have hroot : ∀ x : X, ∃ R ∈ childClusters σ.clusters univ, x ∈ R :=
    fun x => hH.exists_mem_childClusters (by rw [card_univ]; omega) (mem_univ x)
  have hother : ∀ {R : Finset X} {ℓ : X}, ℓ ∈ R → R ≠ {ℓ} → ∃ m ∈ R, m ≠ ℓ := by
    intro R ℓ hℓR hRℓ
    by_contra hcon
    exact hRℓ (eq_singleton_iff_unique_mem.2 ⟨hℓR, fun y hy =>
      Classical.byContradiction fun hyℓ => hcon ⟨y, hy, hyℓ⟩⟩)
  have htriple : ∀ {R : Finset X} {x y z : X}, R ∈ childClusters σ.clusters univ →
      x ∈ R → y ∉ R → (x ∈ A ∨ z ∈ A) → (x ∈ Aᶜ ∨ z ∈ Aᶜ) →
      (∀ R' ∈ childClusters σ.clusters univ,
        (x ∈ R' ↔ x ∈ A) → (y ∈ R' ↔ y ∈ A) → (z ∈ R' ↔ z ∈ A) → False) →
      ∃ S : Finset X, ∃ hS : S.Nonempty, #S = 5 ∧ (A ∩ S).Nonempty ∧ (Aᶜ ∩ S).Nonempty ∧
        A.subtype (· ∈ S) ∉ childClusters (σ.restrict S hS).clusters univ := by
    intro R x y z hR hxR hyR hA3 hAc3 hcon
    obtain ⟨S, hTS, hS5⟩ := rl_exists_five hX (T := {x, y, z}) (card_le_three.trans (by norm_num))
    have hxS : x ∈ S := hTS (by simp)
    have hyS : y ∈ S := hTS (by simp)
    have hzS : z ∈ S := hTS (by simp)
    have hne : ∀ {B : Finset X}, x ∈ B ∨ z ∈ B → (B ∩ S).Nonempty := by
      rintro B (h | h)
      · exact ⟨x, mem_inter.2 ⟨h, hxS⟩⟩
      · exact ⟨z, mem_inter.2 ⟨h, hzS⟩⟩
    refine ⟨S, ⟨x, hxS⟩, hS5, hne hA3, hne hAc3, fun hC => ?_⟩
    have hmrca : ∀ R' ∈ childClusters σ.clusters univ, ¬ S ⊆ R' := fun R' hR' hSR' =>
      hyR (rl_eq_of_mem_childClusters hH hR hR' hxR (hSR' hxS) ▸ hSR' hyS)
    obtain ⟨R', hR', -, hR'eq⟩ := (rl_mem_childClusters_restrict_iff σ ⟨x, hxS⟩ hmrca).1 hC
    exact hcon R' hR' (rl_mem_iff_of_subtype_eq hR'eq x hxS)
      (rl_mem_iff_of_subtype_eq hR'eq y hyS) (rl_mem_iff_of_subtype_eq hR'eq z hzS)
  by_cases hA1 : #A = 1
  · obtain ⟨ℓ, rfl⟩ := card_eq_one.1 hA1
    obtain ⟨R, hR, hℓR⟩ := hroot ℓ
    obtain ⟨m, hmR, hmℓ⟩ := hother hℓR fun e => hAR (e ▸ hR)
    obtain ⟨r, hr⟩ := rl_compl_nonempty (rl_ne_univ_of_mem_childClusters hR)
    refine htriple hR hℓR (mem_compl.1 hr) (Or.inl (mem_singleton_self ℓ))
      (Or.inr (mem_compl.2 (by simpa using hmℓ))) fun R' hR' h1 _ h3 => ?_
    have := rl_eq_of_mem_childClusters hH hR hR' hℓR (h1.2 (mem_singleton_self ℓ))
    subst this
    exact hmℓ (mem_singleton.1 (h3.1 hmR))
  by_cases hAc1 : #Aᶜ = 1
  · obtain ⟨ℓ, hℓ⟩ := card_eq_one.1 hAc1
    have hmemA : ∀ y, y ∈ A ↔ y ≠ ℓ := fun y => by
      rw [← not_iff_not, ← mem_compl, hℓ, mem_singleton, not_not]
    have hℓA : ℓ ∈ Aᶜ := hℓ ▸ mem_singleton_self ℓ
    obtain ⟨R, hR, hℓR⟩ := hroot ℓ
    by_cases hRℓ : R = {ℓ}
    · subst hRℓ
      obtain ⟨y, hy⟩ := hAne
      have hr₁ : y ≠ ℓ := (hmemA y).1 hy
      obtain ⟨R₁, hR₁, hr₁R₁⟩ := hroot y
      have hℓR₁ : ℓ ∉ R₁ := fun h =>
        hr₁ (mem_singleton.1 (rl_eq_of_mem_childClusters hH hR hR₁ (mem_singleton_self ℓ) h ▸ hr₁R₁))
      obtain ⟨r₂, hr₂, hr₂R₁⟩ : ∃ r₂, r₂ ≠ ℓ ∧ r₂ ∉ R₁ := by
        by_contra hcon
        refine hAR ?_
        have hR₁A : R₁ = A := by
          ext z; rw [hmemA]
          exact ⟨fun hz e => hℓR₁ (e ▸ hz),
            fun hz => Classical.byContradiction fun hzR => hcon ⟨z, hz, hzR⟩⟩
        exact hR₁A ▸ hR₁
      refine htriple hR (mem_singleton_self ℓ) (mem_singleton.not.2 hr₁)
        (Or.inr ((hmemA r₂).2 hr₂)) (Or.inl hℓA) fun R' hR' _ h2 h3 => ?_
      have := rl_eq_of_mem_childClusters hH hR₁ hR' hr₁R₁ (h2.2 hy)
      subst this
      exact hr₂R₁ (h3.2 ((hmemA r₂).2 hr₂))
    · obtain ⟨m, hmR, hmℓ⟩ := hother hℓR hRℓ
      obtain ⟨r, hr⟩ := rl_compl_nonempty (rl_ne_univ_of_mem_childClusters hR)
      refine htriple hR hℓR (mem_compl.1 hr) (Or.inr ((hmemA m).2 hmℓ)) (Or.inl hℓA)
        fun R' hR' _ h2 h3 => ?_
      have := rl_eq_of_mem_childClusters hH hR hR' hmR (h3.2 ((hmemA m).2 hmℓ))
      subst this
      exact mem_compl.1 hr (h2.2 ((hmemA r).2 fun e => mem_compl.1 hr (e ▸ hℓR)))
  obtain ⟨a, ha, a', ha', b, hb, b', hb', _, _, hQ⟩ :=
    exists_distinguishing_quartet σ hA (by have := card_pos.2 hAne; omega)
      (by have := card_pos.2 hAcne; omega)
  rw [mem_compl] at hb hb'
  obtain ⟨R₀, hR₀, haR₀⟩ := hroot a
  obtain ⟨w, hw⟩ := rl_compl_nonempty (rl_ne_univ_of_mem_childClusters hR₀)
  obtain ⟨S, hTS, hS5⟩ := rl_exists_five hX (T := {w, a, a', b, b'})
    (le_trans (card_insert_le _ _) (Nat.succ_le_succ
      (le_trans (card_insert_le _ _) (Nat.succ_le_succ card_le_three))))
  have hwS : w ∈ S := hTS (by simp)
  have haS : a ∈ S := hTS (by simp)
  have ha'S : a' ∈ S := hTS (by simp)
  have hbS : b ∈ S := hTS (by simp)
  have hb'S : b' ∈ S := hTS (by simp)
  refine ⟨S, ⟨a, haS⟩, hS5, ⟨a, mem_inter.2 ⟨ha, haS⟩⟩, ⟨b, mem_inter.2 ⟨mem_compl.2 hb, hbS⟩⟩,
    fun hC => ?_⟩
  have hmrca : ∀ R' ∈ childClusters σ.clusters univ, ¬ S ⊆ R' := fun R' hR' hSR' =>
    mem_compl.1 hw (rl_eq_of_mem_childClusters hH hR₀ hR' haR₀ (hSR' haS) ▸ hSR' hwS)
  obtain ⟨R', hR', -, hR'eq⟩ := (rl_mem_childClusters_restrict_iff σ ⟨a, haS⟩ hmrca).1 hC
  have hmem := rl_mem_iff_of_subtype_eq hR'eq
  have hR'U : R' ∈ unroot σ.clusters :=
    mem_unroot.2 (Or.inl ⟨(mem_childClusters.1 hR').1, rl_ne_univ_of_mem_childClusters hR'⟩)
  exact hAR (hQ R' hR'U ((hmem a haS).2 ha) ((hmem a' ha'S).2 ha')
    (mt (hmem b hbS).1 hb) (mt (hmem b' hb'S).1 hb') ▸ hR')

theorem rl_nb_childClusters_univ_eq (hX : 5 ≤ Fintype.card X) {σ σ' : SpeciesTree X}
    (hU : unroot σ.clusters = unroot σ'.clusters)
    (h5 : ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
      (σ.restrict S hS).clusters = (σ'.restrict S hS).clusters) :
    childClusters σ.clusters univ = childClusters σ'.clusters univ := by
  have key : ∀ τ τ' : SpeciesTree X, unroot τ.clusters = unroot τ'.clusters →
      (∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
        (τ.restrict S hS).clusters = (τ'.restrict S hS).clusters) →
      ∀ A ∈ childClusters τ.clusters univ, A ∈ childClusters τ'.clusters univ := by
    intro τ τ' hU h5 A hA
    by_contra hAR
    have hAU : A ∈ unroot τ'.clusters :=
      hU ▸ mem_unroot.2 (Or.inl ⟨(mem_childClusters.1 hA).1, rl_ne_univ_of_mem_childClusters hA⟩)
    obtain ⟨S, hS, hS5, ⟨y, hy⟩, ⟨z, hz⟩, hnot⟩ :=
      rl_nb_exists_five_not_mem_childClusters hX τ' hAU hAR
    rw [← h5 S hS hS5] at hnot
    refine hnot ((rl_mem_childClusters_restrict_iff τ hS fun R hR hSR => ?_).2 ⟨A, hA, ⟨y, hy⟩, rfl⟩)
    have := rl_eq_of_mem_childClusters τ.isHierarchy hA hR (mem_inter.1 hy).1 (hSR (mem_inter.1 hy).2)
    exact mem_compl.1 (mem_inter.1 hz).1 (this ▸ hSR (mem_inter.1 hz).2)
  ext A
  exact ⟨key σ σ' hU h5 A, key σ' σ hU.symm (fun S hS hS5 => (h5 S hS hS5).symm) A⟩

end ADR11
