module

public import ADR11.Trees.Classify
public import ADR11.Computation.Toolkit
public import ADR11.MSC.Marginal

@[expose] public section

namespace ADR11

open Finset Real

abbrev Q1 : Finset (Finset (Fin 4)) := treeOfClusters {{0, 1}}
abbrev Q2 : Finset (Finset (Fin 4)) := treeOfClusters {{0, 2}}
abbrev Q3 : Finset (Finset (Fin 4)) := treeOfClusters {{0, 3}}

theorem unrootedLength_01 (ρ : SpeciesTree (Fin 4)) :
    ρ.unrootedLength {0, 1} =
      (if ({0, 1} : Finset (Fin 4)) ∈ ρ.clusters then ρ.length {0, 1} else 0) +
      (if ({2, 3} : Finset (Fin 4)) ∈ ρ.clusters then ρ.length {2, 3} else 0) := by
  unfold SpeciesTree.unrootedLength
  rw [show ρ.clusters.filter _ = ({{0, 1}, {2, 3}} : Finset _).filter (· ∈ ρ.clusters) by
    ext D; rw [mem_filter, mem_filter, and_comm]; exact and_congr_left' (by revert D; decide),
    sum_filter, sum_pair (by decide)]

section
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype
set_option synthInstance.maxSize 2000

theorem n4_quartets_U4 (τ : SpeciesTree (Fin 4)) {k : ℕ} (hk : k = 0 ∨ k = 1)
    (h : unroot τ.clusters = U4 k) :
    let W := if k = 1 then exp (-τ.unrootedLength {0, 1}) else 1
    τ.unrootedDist id Q1 = 1 - 2 / 3 * W ∧
    τ.unrootedDist id Q2 = 1 / 3 * W ∧
    τ.unrootedDist id Q3 = 1 / 3 * W := by
  let qCode (a : ℕ) : List ℕ := unrootL 4 [1, 2, 4, 8, a, 15]
  have q4_sub : ∀ {H} (hH : IsHierarchy H) (T : BTree) (hwf : T.wfB 4 H = true)
      (htop : T.code = 15) (m : List (ℕ × ℕ)),
      certsB 4 (T.outL 4) [(qCode 3, [(1, []), (-2 / 3, m)]), (qCode 5, [(1 / 3, m)]),
        (qCode 9, [(1 / 3, m)])] = true →
      ∀ (σ : SpeciesTree (Fin 4)), σ.clusters ⊆ H →
        let W := monoVal (fun A => if A ∈ σ.clusters then σ.length A else 0) m
        σ.unrootedDist id Q1 = 1 - 2 / 3 * W ∧ σ.unrootedDist id Q2 = 1 / 3 * W ∧
          σ.unrootedDist id Q3 = 1 / 3 * W := by
    intro H hH T hwf htop m hc σ hsub
    have hd : decF 4 (qCode 3) = Q1 ∧ decF 4 (qCode 5) = Q2 ∧ decF 4 (qCode 9) = Q3 := by decide +kernel
    rw [← hd.1, ← hd.2.1, ← hd.2.2,
      unrootedDist_sub_of_certsB hH T hwf htop hc σ hsub (List.mem_cons_self ..),
      unrootedDist_sub_of_certsB hH T hwf htop hc σ hsub (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      unrootedDist_sub_of_certsB hH T hwf htop hc σ hsub
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))]
    simp only [evalPoly_cons, evalPoly_nil, monoVal_nil]; push_cast
    exact ⟨by ring, by ring, by ring⟩
  have q4_cat : ∀ (ρ : SpeciesTree (Fin 4)), ρ.clusters ⊆ caterpillar4 →
      let W := exp (-ρ.unrootedLength {0, 1})
      ρ.unrootedDist id Q1 = 1 - 2 / 3 * W ∧ ρ.unrootedDist id Q2 = 1 / 3 * W ∧
        ρ.unrootedDist id Q3 = 1 / 3 * W := fun ρ hsub => by
    have hc : decC 4 3 = {0, 1} := by decide +kernel
    have h23 : ({2, 3} : Finset (Fin 4)) ∉ ρ.clusters :=
      fun hm => (by decide : ({2, 3} : Finset (Fin 4)) ∉ caterpillar4) (hsub hm)
    simpa only [monoVal_cons, monoVal_nil, hc, pow_one, mul_one, unrootedLength_01, ite_eq_right h23, add_zero]
      using q4_sub ⟨by decide, by decide, by decide, by decide⟩
        (.bin 15 (.bin 7 (.bin 3 (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf 3))
        (by decide +kernel) rfl [(3, 1)] (by decide +kernel) ρ hsub
  have hr : ∀ (g : Equiv.Perm (Fin 4)) U V, relabelFamily g U = V →
      τ.unrootedDist id U = (τ.relabel g).unrootedDist id V :=
    fun g U V hUV => by rw [← hUV, SpeciesTree.unrootedDist_relabel]
  rcases hk with rfl | rfl
  · simp only [Nat.reduceEqDiff, ↓reduceIte, mul_one]
    let ok (g : Equiv.Perm (Fin 4)) U := relabelFamily g U == Q1 || relabelFamily g U == Q2 || relabelFamily g U == Q3
    have hm := by_unrootB (fun C =>
      ([.refl _, .swap 2 3, .swap 1 3, .swap 0 3] : List (Equiv.Perm (Fin 4))).any fun g =>
        decide (relabelFamily g C ⊆ caterpillar4) && !decide (({0, 1} : Finset (Fin 4)) ∈ relabelFamily g C) &&
        !decide (({2, 3} : Finset (Fin 4)) ∈ relabelFamily g C) && ok g Q1 && ok g Q2 && ok g Q3) (by decide +kernel) h
    simp only [List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not] at hm
    obtain ⟨g, -, ⟨⟨⟨⟨⟨hsub, h01⟩, h23⟩, h1⟩, h2⟩, h3⟩⟩ := hm
    obtain ⟨q1, q2, q3⟩ := q4_cat (τ.relabel g) hsub
    rw [unrootedLength_01, SpeciesTree.relabel_clusters, ite_eq_right h01,
      ite_eq_right h23, add_zero, neg_zero, exp_zero] at q1 q2 q3
    have hq : ∀ U, ok g U = true → τ.unrootedDist id U = 1 / 3 := fun U hU => by
      simp only [ok, Bool.or_eq_true, beq_iff_eq] at hU
      rcases hU with (e | e) | e <;> rw [hr g U _ e] <;> linarith
    exact ⟨by linarith [hq Q1 h1], hq Q2 h2, hq Q3 h3⟩
  · simp only [↓reduceIte]
    let p4 : Equiv.Perm (Fin 4) := (Equiv.swap 0 2).trans (Equiv.swap 1 3)
    have hm := by_unrootB (fun C => decide (C ⊆ hierarchyOf {{0, 1}, {2, 3}}) ||
      ([.refl _, .swap 2 3, p4, p4.trans (.swap 2 3)] : List (Equiv.Perm (Fin 4))).any fun g =>
        let A := ({0, 1} : Finset (Fin 4)).map g.symm.toEmbedding
        decide (relabelFamily g C ⊆ caterpillar4) && (A == {0, 1} || A == ({0, 1} : Finset (Fin 4))ᶜ) &&
        (relabelFamily g Q1 == Q1) && ((relabelFamily g Q2 == Q2 && relabelFamily g Q3 == Q3) ||
          (relabelFamily g Q2 == Q3 && relabelFamily g Q3 == Q2))) (by decide +kernel) h
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hm
    rcases hm with hsub | ⟨g, -, ⟨⟨⟨hsub, hA01⟩, hg1⟩, hg23⟩⟩
    · have hc : decC 4 3 = {0, 1} ∧ decC 4 12 = {2, 3} := by decide +kernel
      simpa only [monoVal_cons, monoVal_nil, hc.1, hc.2, pow_one, mul_one, unrootedLength_01,
        neg_add, exp_add] using q4_sub ⟨by decide, by decide, by decide, by decide⟩
          (.bin 15 (.bin 3 (.leaf 0) (.leaf 1)) (.bin 12 (.leaf 2) (.leaf 3)))
          (by decide +kernel) rfl [(3, 1), (12, 1)] (by decide +kernel) τ hsub
    · let A := ({0, 1} : Finset (Fin 4)).map g.symm.toEmbedding
      have hAg : A.map g.toEmbedding = {0, 1} := by simp [A]
      obtain ⟨e1, e2, e3⟩ := q4_cat (τ.relabel g) hsub
      have hul : (τ.relabel g).unrootedLength {0, 1} = τ.unrootedLength {0, 1} := by
        conv_lhs => rw [← hAg, SpeciesTree.unrootedLength_relabel]
        dsimp only [A]; rcases hA01 with hA | hA <;> rw [hA]
        unfold SpeciesTree.unrootedLength; simp only [compl_compl, or_comm]
      rw [hul] at e1 e2 e3
      rcases hg23 with ⟨h2, h3⟩ | ⟨h2, h3⟩
      · exact ⟨(hr g _ _ hg1).trans e1, (hr g _ _ h2).trans e2, (hr g _ _ h3).trans e3⟩
      · exact ⟨(hr g _ _ hg1).trans e1, (hr g _ _ h2).trans e3, (hr g _ _ h3).trans e2⟩

end

variable {X : Type*} [DecidableEq X]

theorem mem_restrictClusters {S : Finset X} {H : Finset (Finset X)} {C : Finset S} :
    C ∈ restrictClusters S H ↔ ∃ A ∈ H, (A ∩ S).Nonempty ∧ A.subtype (· ∈ S) = C := by
  simp [restrictClusters, and_assoc]

theorem subtype_mem_restrictClusters {S : Finset X} {H : Finset (Finset X)} {A : Finset X}
    (hA : A ∈ H) (hAS : (A ∩ S).Nonempty) : A.subtype (· ∈ S) ∈ restrictClusters S H :=
  mem_restrictClusters.2 ⟨A, hA, hAS, rfl⟩

theorem mem_iff_of_subtype_eq {S A B : Finset X}
    (h : A.subtype (· ∈ S) = B.subtype (· ∈ S)) {x : X} (hx : x ∈ S) : x ∈ A ↔ x ∈ B := by
  simpa only [mem_subtype, eq_iff_iff] using congrArg ((⟨x, hx⟩ : S) ∈ ·) h

theorem card_quartet {A : Finset X} {a a' b b' : X} (ha : a ∈ A) (ha' : a' ∈ A)
    (hb : b ∉ A) (hb' : b' ∉ A) (haa : a ≠ a') (hbb : b ≠ b') : #({a, a', b, b'} : Finset X) = 4 := by
  have ne : ∀ {x y}, x ∈ A → y ∉ A → x ≠ y := fun hx hy e => hy (e ▸ hx)
  rw [card_insert_of_notMem (by simp [haa, ne ha hb, ne ha hb']),
    card_insert_of_notMem (by simp [ne ha' hb, ne ha' hb']), card_pair hbb]

variable [Fintype X]

theorem unrootedDist_eq_iff_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' := by
  obtain ⟨e, k, hk, he⟩ := exists_equiv_unroot_eq_U4 hX σ
  simp only [mem_insert, mem_singleton] at hk
  rw [← SpeciesTree.unrootedDist_relabel_eq_iff σ σ' e.symm,
    ← SpeciesTree.sameUnrootedMetricTree_relabel_iff σ σ' e.symm]
  generalize σ.relabel e.symm = τ at he ⊢
  generalize σ'.relabel e.symm = τ' at ⊢
  refine ⟨fun hd => ?_, fun ⟨hU, hL⟩ => funext fun U => ?_⟩
  · have hq0 : ∀ ρ : SpeciesTree (Fin 4), unroot ρ.clusters = U4 0 →
        ρ.unrootedDist id Q1 = 1 / 3 ∧ ρ.unrootedDist id Q2 = 1 / 3 ∧ ρ.unrootedDist id Q3 = 1 / 3 :=
      fun ρ hρ => by
        obtain ⟨q1, q2, q3⟩ := n4_quartets_U4 ρ (Or.inl rfl) hρ
        simp only [Nat.reduceEqDiff, ↓reduceIte] at q1 q2 q3
        exact ⟨by linarith, by linarith, by linarith⟩
    have hq1 : ∀ ρ : SpeciesTree (Fin 4), unroot ρ.clusters = U4 1 →
        ρ.unrootedDist id Q1 = 1 - 2 / 3 * exp (-ρ.unrootedLength {0, 1}) ∧
        1 / 3 < ρ.unrootedDist id Q1 ∧ ρ.unrootedDist id Q2 < 1 / 3 ∧
        ρ.unrootedDist id Q3 < 1 / 3 := fun ρ hρ => by
      obtain ⟨q1, q2, q3⟩ := n4_quartets_U4 ρ (Or.inr rfl) hρ
      simp only [↓reduceIte] at q1 q2 q3
      have hpos : 0 < ρ.unrootedLength {0, 1} := sum_pos
        (fun C hC => ρ.length_pos C (mem_filter.1 hC).1 (mem_filter.1 hC).2.1) <| by
        have hA : ({0, 1} : Finset (Fin 4)) ∈ unroot ρ.clusters := by rw [hρ]; decide
        rcases mem_unroot.1 hA with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨{0, 1}, mem_filter.2 ⟨h1, h2, Or.inl rfl⟩⟩
        · exact ⟨({0, 1} : Finset (Fin 4))ᶜ, mem_filter.2 ⟨h1, h2, Or.inr rfl⟩⟩
      have hlt1 : exp (-ρ.unrootedLength {0, 1}) < 1 := exp_lt_one_iff.2 (neg_lt_zero.2 hpos)
      exact ⟨q1, by linarith, by linarith, by linarith⟩
    have hsw : ∀ (g : Equiv.Perm (Fin 4)) U V, relabelFamily g U = V →
        τ'.unrootedDist id U = (τ'.relabel g).unrootedDist id V :=
      fun g U V hUV => by rw [← hUV, SpeciesTree.unrootedDist_relabel]
    have hle : τ'.unrootedDist id Q2 ≤ 1 / 3 ∧ τ'.unrootedDist id Q3 ≤ 1 / 3 := by
      rw [← hd]; rcases hk with rfl | rfl
      exacts [⟨(hq0 τ he).2.1.le, (hq0 τ he).2.2.le⟩, ⟨(hq1 τ he).2.2.1.le, (hq1 τ he).2.2.2.le⟩]
    have h' : unroot τ'.clusters = U4 0 ∨ unroot τ'.clusters = U4 1 := by
      obtain ⟨e', k', hk', he'⟩ := exists_equiv_unroot_eq_U4 (Fintype.card_fin 4) τ'
      have hu : unroot τ'.clusters = relabelFamily e' (U4 k') := by
        rw [← he', SpeciesTree.relabel_clusters, unroot_relabelFamily]
        simp [relabelFamily, ← Equiv.finsetCongr_symm]
      rcases (by simpa using hk' : k' = 0 ∨ k' = 1) with rfl | rfl
      · exact Or.inl (hu.trans ((by decide +kernel : ∀ g : Equiv.Perm (Fin 4), relabelFamily g (U4 0) = U4 0) e'))
      · rcases (by decide +kernel : ∀ g : Equiv.Perm (Fin 4), relabelFamily g (U4 1) = U4 1 ∨
          relabelFamily (Equiv.swap 1 2) (relabelFamily g (U4 1)) = U4 1 ∨
          relabelFamily (Equiv.swap 1 3) (relabelFamily g (U4 1)) = U4 1) e' with h1 | h2 | h3
        · exact Or.inr (hu.trans h1)
        · linarith [(hq1 (τ'.relabel (.swap 1 2)) (by simpa [unroot_relabelFamily, hu] using h2)).2.1,
            hsw (.swap 1 2) Q2 Q1 (by decide), hle.1]
        · linarith [(hq1 (τ'.relabel (.swap 1 3)) (by simpa [unroot_relabelFamily, hu] using h3)).2.1,
            hsw (.swap 1 3) Q3 Q1 (by decide), hle.2]
    rcases hk with rfl | rfl <;> rcases h' with h' | h'
    · refine ⟨he.trans h'.symm, fun A hA h2 h2c => absurd h2c ?_⟩; revert A hA h2; rw [he]; decide
    · linarith [(hq0 τ he).1, hd ▸ (hq1 τ' h').2.1]
    · linarith [hd ▸ (hq1 τ he).2.1, (hq0 τ' h').1]
    · refine ⟨he.trans h'.symm, fun A hA h2 h2c => ?_⟩
      have hl : τ.unrootedLength {0, 1} = τ'.unrootedLength {0, 1} := by
        linarith [exp_injective (show exp (-τ.unrootedLength {0, 1}) = exp (-τ'.unrootedLength {0, 1}) by
          linarith [hd ▸ (hq1 τ he).1, (hq1 τ' h').1])]
      rcases (show A = {0, 1} ∨ A = ({0, 1} : Finset (Fin 4))ᶜ by
        revert A hA h2 h2c; rw [he]; decide) with rfl | rfl
      · exact hl
      · simpa only [SpeciesTree.unrootedLength, compl_compl, or_comm] using hl
  · have hdist : ∀ ρ : SpeciesTree (Fin 4), unroot ρ.clusters = U4 k →
        let W := if k = 1 then exp (-ρ.unrootedLength {0, 1}) else 1
        ρ.unrootedDist id U = if U = Q1 then 1 - 2 / 3 * W else if U = Q2 then 1 / 3 * W
          else if U = Q3 then 1 / 3 * W else 0 := fun ρ hρ => by
      obtain ⟨q1, q2, q3⟩ := n4_quartets_U4 ρ hk hρ
      dsimp only at q1 q2 q3 ⊢
      set W := if k = 1 then exp (-ρ.unrootedLength {0, 1}) else 1
      split_ifs with h1 h2 h3
      · exact h1 ▸ q1
      · exact h2 ▸ q2
      · exact h3 ▸ q3
      · let S : Finset (Finset (Finset (Fin 4))) := {Q1, Q2, Q3}
        have hS : ∑ T ∈ S, ρ.unrootedDist id T = 1 := by
          rw [sum_insert (by decide), sum_pair (by decide), q1, q2, q3]; ring
        have h0 : ∑ T ∈ univ \ S, ρ.unrootedDist id T = 0 := by
          linarith [sum_sdiff (subset_univ S) (f := ρ.unrootedDist id), unrootedDist_sum ρ id]
        exact (sum_eq_zero_iff_of_nonneg fun T _ => unrootedDist_nonneg ρ id T).1 h0 U
          (mem_sdiff.2 ⟨mem_univ U, by simp [S, h1, h2, h3]⟩)
    rw [hdist τ he, hdist τ' (hU.symm.trans he)]
    rcases hk with rfl | rfl
    · rfl
    · simp only [↓reduceIte]; rw [hL {0, 1} (by rw [he]; decide) (by decide) (by decide)]

theorem SpeciesTree.unrootedLength_of_compl_notMem (σ : SpeciesTree X) {A : Finset X}
    (hA : A ∈ σ.clusters) (hAu : A ≠ univ) (hAc : Aᶜ ∉ σ.clusters) :
    σ.unrootedLength A = σ.length A :=
  sum_eq_single_of_mem A (mem_filter.2 ⟨hA, hAu, Or.inl rfl⟩) fun _ hC hCA =>
    (mem_filter.1 hC).2.2.elim (absurd · hCA) fun e => absurd (e ▸ (mem_filter.1 hC).1) hAc

theorem subtype_compl {S : Finset X} (A : Finset X) :
    Aᶜ.subtype (· ∈ S) = (A.subtype (· ∈ S))ᶜ := by ext; simp [mem_subtype, mem_compl]

theorem subtype_ne_univ_iff {S A : Finset X} :
    A.subtype (· ∈ S) ≠ univ ↔ (Aᶜ ∩ S).Nonempty := by
  rw [← subtype_nonempty_iff, subtype_compl, Ne, ← compl_eq_empty_iff,
    ← not_nonempty_iff_eq_empty, not_not]

lemma mem_unroot_restrict {σ : SpeciesTree X} {S : Finset X} {hS : S.Nonempty}
    {C : Finset S} :
    C ∈ unroot (σ.restrict S hS).clusters ↔
      ∃ A ∈ unroot σ.clusters, (A ∩ S).Nonempty ∧ (Aᶜ ∩ S).Nonempty ∧ A.subtype (· ∈ S) = C := by
  simp only [mem_unroot]; dsimp only [SpeciesTree.restrict]
  constructor
  · rintro (⟨hC, hCu⟩ | ⟨hC, hCu⟩)
    · obtain ⟨A, hA, hAS, rfl⟩ := mem_restrictClusters.1 hC
      exact ⟨A, Or.inl ⟨hA, fun e => hCu (e ▸ subtype_univ _)⟩, hAS, subtype_ne_univ_iff.1 hCu, rfl⟩
    · obtain ⟨A, hA, hAS, hAC⟩ := mem_restrictClusters.1 hC
      exact ⟨Aᶜ, Or.inr ⟨by rwa [compl_compl], fun e => hCu (hAC ▸ compl_compl A ▸ e ▸ subtype_univ _)⟩,
        subtype_ne_univ_iff.1 (hAC ▸ hCu), by rwa [compl_compl], by rw [subtype_compl, hAC, compl_compl]⟩
  · rintro ⟨A, hA, hAS, hAcS, rfl⟩
    rcases hA with ⟨hA', -⟩ | ⟨hA', -⟩
    · exact Or.inl ⟨subtype_mem_restrictClusters hA' hAS, subtype_ne_univ_iff.2 hAcS⟩
    · rw [← subtype_compl]
      exact Or.inr ⟨subtype_mem_restrictClusters hA' hAcS, subtype_ne_univ_iff.2 (by rwa [compl_compl])⟩

theorem exists_pair_max (σ : SpeciesTree X) {N : Finset X} (hN : 2 ≤ #N) :
    ∃ x ∈ N, ∃ y ∈ N, x ≠ y ∧ ∀ C ∈ σ.clusters, x ∈ C → y ∈ C → ¬ C ⊂ N := by
  obtain ⟨x, hx⟩ : N.Nonempty := card_pos.1 (by omega)
  obtain ⟨M, hM, hMmax⟩ := (σ.clusters.filter fun C => x ∈ C ∧ C ⊂ N).exists_max_image card
    ⟨{x}, mem_filter.2 ⟨σ.singleton_mem x, mem_singleton_self x,
      (singleton_subset_iff.2 hx).ssubset_of_ne fun e => by subst e; simp at hN⟩⟩
  obtain ⟨hMc, hxM, hMN⟩ := mem_filter.1 hM
  obtain ⟨y, hyN, hyM⟩ := exists_of_ssubset hMN
  refine ⟨x, hx, y, hyN, fun e => hyM (e ▸ hxM), fun C hC hxC hyC hCN => ?_⟩
  rcases σ.isHierarchy.subset_or_subset_of_mem hC hMc hxC hxM with h | h
  · exact hyM (h hyC)
  · exact hyM (eq_of_subset_of_card_le h (hMmax C (mem_filter.2 ⟨hC, hxC, hCN⟩)) ▸ hyC)

theorem exists_distinguishing_quartet (σ : SpeciesTree X) {A : Finset X}
    (hA : A ∈ unroot σ.clusters) (hA₁ : 2 ≤ #A) (hA₂ : 2 ≤ #Aᶜ) :
    ∃ a ∈ A, ∃ a' ∈ A, ∃ b ∈ Aᶜ, ∃ b' ∈ Aᶜ, a ≠ a' ∧ b ≠ b' ∧
      ∀ C ∈ unroot σ.clusters, a ∈ C → a' ∈ C → b ∉ C → b' ∉ C → C = A := by
  have go : ∀ {A : Finset X}, A ∈ σ.clusters → A ≠ univ → 2 ≤ #A → 2 ≤ #Aᶜ →
      ∃ a ∈ A, ∃ a' ∈ A, ∃ b ∈ Aᶜ, ∃ b' ∈ Aᶜ, a ≠ a' ∧ b ≠ b' ∧
        ∀ C ∈ unroot σ.clusters, a ∈ C → a' ∈ C → b ∉ C → b' ∉ C → C = A :=
    fun {A} hA hAu hA₁ hA₂ => by
      obtain ⟨z, hz⟩ : A.Nonempty := card_pos.1 (by omega)
      obtain ⟨a, ha, a', ha', haa, hpair⟩ := exists_pair_max σ hA₁
      have hup : ∀ C ∈ σ.clusters, a ∈ C → a' ∈ C → A ⊆ C := fun C hC h1 h2 =>
        (σ.isHierarchy.subset_or_subset_of_mem hC hA h1 ha).elim
          (fun h => by by_contra hne; exact hpair C hC h1 h2 (h.ssubset_of_ne fun e => hne (e ▸ subset_rfl))) id
      obtain ⟨P, hP, hPmin⟩ := (σ.clusters.filter (A ⊂ ·)).exists_min_image card
        ⟨univ, mem_filter.2 ⟨σ.univ_mem, ssubset_univ_iff.2 hAu⟩⟩
      obtain ⟨hPc, hAP⟩ := mem_filter.1 hP
      have hPle : ∀ C ∈ σ.clusters, A ⊂ C → P ⊆ C := fun C hC hAC =>
        (σ.isHierarchy.subset_or_subset_of_mem hC hPc (hAC.1 hz) (hAP.1 hz)).elim
          (fun h => eq_of_subset_of_card_le h (hPmin C (mem_filter.2 ⟨hC, hAC⟩)) ▸ subset_rfl) id
      obtain ⟨b, hb, b', hb', hbb, hP1, hP2⟩ : ∃ b ∈ Aᶜ, ∃ b' ∈ Aᶜ, b ≠ b' ∧
          (∀ C ∈ σ.clusters, A ⊂ C → b ∈ C ∨ b' ∈ C) ∧
          (∀ D ∈ σ.clusters, b ∈ D → b' ∈ D → ¬ D ⊂ Aᶜ) := by
        by_cases hPu : P = univ
        · obtain ⟨b, hb, b', hb', hbb, h⟩ := exists_pair_max σ hA₂
          exact ⟨b, hb, b', hb', hbb, fun C hC hAC => Or.inl (hPle C hC hAC (hPu ▸ mem_univ b)), h⟩
        · obtain ⟨b, hbP, hbA⟩ := exists_of_ssubset hAP
          obtain ⟨b', hb'⟩ : Pᶜ.Nonempty := nonempty_iff_ne_empty.2 fun h => hPu ((compl_eq_empty_iff P).1 h)
          rw [mem_compl] at hb'
          refine ⟨b, mem_compl.2 hbA, b', mem_compl.2 fun h => hb' (hAP.1 h),
            fun e => hb' (e ▸ hbP), fun C hC hAC => Or.inl (hPle C hC hAC hbP), fun D hD hbD hb'D hDA => ?_⟩
          rcases σ.isHierarchy.subset_or_subset_of_mem hD hPc hbD hbP with h | h
          · exact hb' (h hb'D)
          · exact mem_compl.1 (hDA.1 (h (hAP.1 hz))) hz
      refine ⟨a, ha, a', ha', b, hb, b', hb', haa, hbb, fun C hC haC ha'C hbC hb'C => ?_⟩
      rcases mem_unroot.1 hC with ⟨hC1, -⟩ | ⟨hC1, -⟩
      · by_contra hne
        exact (hP1 C hC1 ((hup C hC1 haC ha'C).ssubset_of_ne (Ne.symm hne))).elim hbC hb'C
      · have hbD := mem_compl.2 hbC; have hb'D := mem_compl.2 hb'C
        have hDA : Cᶜ ⊆ Aᶜ := (σ.laminar Cᶜ hC1 A hA).elim (fun h => absurd (h hbD) (mem_compl.1 hb))
          fun h => h.elim (fun h => absurd haC (mem_compl.1 (h ha))) subset_compl_iff_disjoint_right.2
        exact compl_injective (by by_contra hne; exact hP2 Cᶜ hC1 hbD hb'D (hDA.ssubset_of_ne hne))
  rcases mem_unroot.1 hA with ⟨hA1, hA2⟩ | ⟨hA1, hA2⟩
  · exact go hA1 hA2 hA₁ hA₂
  · obtain ⟨a, ha, a', ha', b, hb, b', hb', haa, hbb, h⟩ := go hA1 hA2 hA₂ (by rwa [compl_compl])
    rw [compl_compl] at hb hb'
    refine ⟨b, hb, b', hb', a, ha, a', ha', hbb, haa, fun C hC hbC hb'C haC ha'C => compl_injective ?_⟩
    exact h Cᶜ (compl_mem_unroot.2 hC) (mem_compl.2 haC) (mem_compl.2 ha'C)
      (fun h' => mem_compl.1 h' hbC) (fun h' => mem_compl.1 h' hb'C)

theorem sameUnrootedMetricTree_of_unrootedDist_eq (σ σ' : SpeciesTree X)
    (hd : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameUnrootedMetricTree σ' := by
  have h : ∀ Q : Finset X, ∀ hQ : Q.Nonempty, #Q = 4 →
      (σ.restrict Q hQ).SameUnrootedMetricTree (σ'.restrict Q hQ) := fun Q hQ hQ4 =>
    (unrootedDist_eq_iff_four (by simpa using hQ4) _ _).1 (unrootedDist_restrict_eq hd Q hQ)
  have usub : ∀ τ τ' : SpeciesTree X,
      (∀ Q : Finset X, ∀ hQ : Q.Nonempty, #Q = 4 →
        unroot (τ.restrict Q hQ).clusters = unroot (τ'.restrict Q hQ).clusters) →
      unroot τ.clusters ⊆ unroot τ'.clusters := fun τ τ' hq A hA => by
    have hAne := (nonempty_of_mem_unroot τ.isHierarchy hA).1
    have hAcne := (nonempty_of_mem_unroot τ.isHierarchy (compl_mem_unroot.2 hA)).1
    by_cases h1 : #A ≤ 1
    · obtain ⟨x, rfl⟩ := card_eq_one.1 (le_antisymm h1 (card_pos.2 hAne))
      exact mem_unroot.2 (Or.inl ⟨τ'.singleton_mem x,
        fun hu => not_nonempty_empty (by rw [hu, compl_univ] at hAcne; exact hAcne)⟩)
    by_cases h2 : #Aᶜ ≤ 1
    · obtain ⟨x, hx⟩ := card_eq_one.1 (le_antisymm h2 (card_pos.2 hAcne))
      exact mem_unroot.2 (Or.inr ⟨hx ▸ τ'.singleton_mem x, fun hu =>
        hAne.ne_empty (by rw [← compl_compl A, hu, compl_univ])⟩)
    have hqt : ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ Aᶜ, ∀ b' ∈ Aᶜ, a ≠ a' → b ≠ b' →
        ∃ C ∈ unroot τ'.clusters, a ∈ C ∧ a' ∈ C ∧ b ∉ C ∧ b' ∉ C := by
      intro a ha a' ha' b hb b' hb' haa hbb
      rw [mem_compl] at hb hb'
      let Q : Finset X := {a, a', b, b'}
      have hQ : Q.Nonempty := insert_nonempty _ _
      have h1' : A.subtype (· ∈ Q) ∈ unroot (τ'.restrict Q hQ).clusters := by
        rw [← hq Q hQ (card_quartet ha ha' hb hb' haa hbb), mem_unroot_restrict]
        exact ⟨A, hA, ⟨a, mem_inter.2 ⟨ha, by simp [Q]⟩⟩, ⟨b, mem_inter.2 ⟨mem_compl.2 hb, by simp [Q]⟩⟩, rfl⟩
      obtain ⟨C, hC, -, -, hCA⟩ := mem_unroot_restrict.1 h1'
      have key := fun (x : X) (hx : x ∈ Q) => mem_iff_of_subtype_eq hCA hx
      exact ⟨C, hC, (key a (by simp [Q])).2 ha, (key a' (by simp [Q])).2 ha',
        mt (key b (by simp [Q])).1 hb, mt (key b' (by simp [Q])).1 hb'⟩
    obtain ⟨b₀, hb₀⟩ := hAcne
    obtain ⟨b₁, hb₁, hb₁₀⟩ := exists_mem_ne (show 1 < #Aᶜ by omega) b₀
    set F := insert univ ((unroot τ'.clusters).filter fun C => b₀ ∉ C)
    have sub_or_sub : ∀ {C D}, C ∈ F → D ∈ F → ∀ {x}, x ∈ C → x ∈ D → C ⊆ D ∨ D ⊆ C := by
      intro C D hC hD x hxC hxD
      rcases mem_insert.1 hC with rfl | hC; · exact Or.inr (subset_univ _)
      rcases mem_insert.1 hD with rfl | hD; · exact Or.inl (subset_univ _)
      obtain ⟨hCU, hC₀⟩ := mem_filter.1 hC; obtain ⟨hDU, hD₀⟩ := mem_filter.1 hD
      rcases unroot_compat τ' hCU hDU with h | h | h | h
      · exact absurd hxD (disjoint_left.1 h hxC)
      · exact Or.inl (disjoint_compl_right_iff.1 h)
      · exact Or.inr (disjoint_compl_left_iff.1 h)
      · exact absurd (mem_compl.2 hD₀) (disjoint_left.1 h (mem_compl.2 hC₀))
    have htri : ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∉ A, ∃ C ∈ F, a ∈ C ∧ a' ∈ C ∧ b ∉ C := fun a ha a' ha' b hb => by
      by_cases haa : a = a'
      · refine ⟨{a}, mem_insert_of_mem (mem_filter.2 ⟨mem_unroot.2 (Or.inl ⟨τ'.singleton_mem a,
          fun hu => h2 ((card_le_card (subset_univ Aᶜ)).trans (by rw [← hu]; simp))⟩),
          fun e => mem_compl.1 hb₀ (mem_singleton.1 e ▸ ha)⟩),
          mem_singleton_self a, haa ▸ mem_singleton_self a, fun e => hb (mem_singleton.1 e ▸ ha)⟩
      · by_cases hbb : b = b₀
        · subst hbb
          obtain ⟨C, hC, h1, h2', -, h4⟩ := hqt a ha a' ha' b₁ hb₁ b hb₀ haa hb₁₀
          exact ⟨C, mem_insert_of_mem (mem_filter.2 ⟨hC, h4⟩), h1, h2', h4⟩
        · obtain ⟨C, hC, h1, h2', h3, h4⟩ := hqt a ha a' ha' b (mem_compl.2 hb) b₀ hb₀ haa hbb
          exact ⟨C, mem_insert_of_mem (mem_filter.2 ⟨hC, h4⟩), h1, h2', h3⟩
    obtain ⟨a₀, ha₀⟩ := hAne
    obtain ⟨M, hM, hMmin⟩ := (F.filter (A ⊆ ·)).exists_min_image card
      ⟨univ, mem_filter.2 ⟨mem_insert_self _ _, subset_univ A⟩⟩
    obtain ⟨hMF, hAM⟩ := mem_filter.1 hM
    have hMA : M ⊆ A := fun b hbM => by
      by_contra hbA
      obtain ⟨C₀, hC₀, haC₀, -, hbC₀⟩ := htri a₀ ha₀ a₀ ha₀ b hbA
      obtain ⟨C, hC, hCmax⟩ := (F.filter fun C => a₀ ∈ C ∧ b ∉ C).exists_max_image card
        ⟨C₀, mem_filter.2 ⟨hC₀, haC₀, hbC₀⟩⟩
      obtain ⟨hCF, haC, hbC⟩ := mem_filter.1 hC
      have hAC : A ⊆ C := fun a' ha' => by
        obtain ⟨D, hD, haD, ha'D, hbD⟩ := htri a₀ ha₀ a' ha' b hbA
        rcases sub_or_sub hCF hD haC haD with hCD | hDC
        · exact eq_of_subset_of_card_le hCD (hCmax D (mem_filter.2 ⟨hD, haD, hbD⟩)) ▸ ha'D
        · exact hDC ha'D
      rcases sub_or_sub hCF hMF haC (hAM ha₀) with hCM | hMC
      · exact not_lt.2 (hMmin C (mem_filter.2 ⟨hCF, hAC⟩))
          (card_lt_card (hCM.ssubset_of_ne fun e => hbC (e ▸ hbM)))
      · exact hbC (hMC hbM)
    rcases mem_insert.1 (Subset.antisymm hAM hMA ▸ hMF : A ∈ F) with rfl | hk
    · exact absurd (mem_univ b₀) (mem_compl.1 hb₀)
    · exact (mem_filter.1 hk).1
  have hU := Subset.antisymm (usub σ σ' fun Q hQ hQ4 => (h Q hQ hQ4).1)
    (usub σ' σ fun Q hQ hQ4 => (h Q hQ hQ4).1.symm)
  refine ⟨hU, fun A hA hA₁ hA₂ => ?_⟩
  obtain ⟨a, ha, a', ha', b, hb, b', hb', haa, hbb, huniq⟩ := exists_distinguishing_quartet σ hA hA₁ hA₂
  rw [mem_compl] at hb hb'
  let Q : Finset X := {a, a', b, b'}
  have hQ : Q.Nonempty := insert_nonempty _ _
  obtain ⟨hUQ, hLQ⟩ := h Q hQ (card_quartet ha ha' hb hb' haa hbb)
  set C := A.subtype (· ∈ Q)
  have hC₀ : C ∈ unroot (σ.restrict Q hQ).clusters := mem_unroot_restrict.2
    ⟨A, hA, ⟨a, mem_inter.2 ⟨ha, by simp [Q]⟩⟩, ⟨b, mem_inter.2 ⟨mem_compl.2 hb, by simp [Q]⟩⟩, rfl⟩
  have hC₀₁ : 2 ≤ #C :=
    one_lt_card.2 ⟨⟨a, by simp [Q]⟩, mem_subtype.2 ha, ⟨a', by simp [Q]⟩, mem_subtype.2 ha',
      fun e => haa (congrArg Subtype.val e)⟩
  have hC₀₂ : 2 ≤ #Cᶜ :=
    one_lt_card.2 ⟨⟨b, by simp [Q]⟩, by simp [C, hb], ⟨b', by simp [Q]⟩, by simp [C, hb'],
      fun e => hbb (congrArg Subtype.val e)⟩
  obtain ⟨hCne, hCu⟩ := nonempty_of_mem_unroot (σ.restrict Q hQ).isHierarchy hC₀
  obtain ⟨hCcne, hCcu⟩ := nonempty_of_mem_unroot (σ.restrict Q hQ).isHierarchy (compl_mem_unroot.2 hC₀)
  have hlen : ∀ τ : SpeciesTree X, (∀ B ∈ unroot τ.clusters, a ∈ B → a' ∈ B → b ∉ B → b' ∉ B → B = A) →
      (τ.restrict Q hQ).unrootedLength C = τ.unrootedLength A := fun τ huniqτ => by
    have eqA : ∀ {D}, D ∈ unroot τ.clusters → D.subtype (· ∈ Q) = C → D = A := fun hD hDC => by
      have key := fun (x : X) (hx : x ∈ Q) => mem_iff_of_subtype_eq hDC hx
      exact huniqτ _ hD ((key a (by simp [Q])).2 ha) ((key a' (by simp [Q])).2 ha')
        (mt (key b (by simp [Q])).1 hb) (mt (key b' (by simp [Q])).1 hb')
    set p : Finset X → Prop := fun B => B.subtype (· ∈ Q) = C ∨ B.subtype (· ∈ Q) = Cᶜ
    unfold SpeciesTree.unrootedLength; dsimp only [SpeciesTree.restrict]
    trans ∑ B ∈ τ.clusters with B ≠ univ ∧ p B, τ.length B
    · symm
      rw [← sum_fiberwise_of_maps_to (g := fun B : Finset X => B.subtype (· ∈ Q))
        (t := (restrictClusters Q τ.clusters).filter (fun D => D ≠ univ ∧ (D = C ∨ D = Cᶜ)))]
      · refine sum_congr rfl fun D hD => ?_
        unfold SpeciesTree.restrictLength; rw [filter_filter]
        exact sum_congr (filter_congr fun B _ =>
          ⟨fun ⟨⟨h2, _⟩, h3⟩ => ⟨h2, h3⟩,
           fun ⟨h2, h3⟩ => ⟨⟨h2, by show B.subtype _ = _ ∨ _; rw [h3]; exact (mem_filter.1 hD).2.2⟩, h3⟩⟩)
          fun _ _ => rfl
      · intro B hB; obtain ⟨hB1, -, hB3⟩ := mem_filter.1 hB
        exact mem_filter.2 ⟨mem_restrictClusters.2 ⟨B, hB1, subtype_nonempty_iff.1
          (by rcases hB3 with h | h <;> rwa [h]), rfl⟩, by rcases hB3 with h | h <;> rwa [h], hB3⟩
    · refine sum_congr (filter_congr fun B hB => and_congr_right fun hBu => ?_) fun _ _ => rfl
      refine ⟨fun h => ?_, fun h => h.elim (fun e => e ▸ Or.inl rfl) fun e => e ▸ Or.inr (subtype_compl A)⟩
      have hBU : B ∈ unroot τ.clusters := mem_unroot.2 (Or.inl ⟨hB, hBu⟩)
      exact h.imp (eqA hBU) fun h' => compl_inj_iff.1 <| by
        rw [compl_compl]; exact eqA (compl_mem_unroot.2 hBU) (by rw [subtype_compl, h', compl_compl])
  rw [← hlen σ huniq, ← hlen σ' (hU ▸ huniq)]
  exact hLQ _ hC₀ hC₀₁ hC₀₂

end ADR11
