module

public import ADR11.MSC.Basic

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

universe v

lemma marg_sum_ite_comp {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [DecidableEq γ] (f : α → β) (g : β → γ) (p : α → ℝ) (c : γ) :
    ∑ b, (if g b = c then ∑ a, (if f a = b then p a else 0) else 0) =
      ∑ a, if g (f a) = c then p a else 0 := by
  simp_rw [show ∀ b, (if g b = c then ∑ a, (if f a = b then p a else 0) else 0) =
    ∑ a, if f a = b then (if g b = c then p a else 0) else 0 from fun b => by split_ifs <;> simp]
  rw [sum_comm]; exact sum_congr rfl fun a _ => by rw [sum_ite_eq]; simp

theorem unrootedDist_comp_eq {L L' : Type v} [Fintype L] [DecidableEq L] [Fintype L'] [DecidableEq L']
    {σ σ' : SpeciesTree X} {s : L → X} (h : σ.unrootedDist s = σ'.unrootedDist s) (e : L' ↪ L) :
    σ.unrootedDist (s ∘ e) = σ'.unrootedDist (s ∘ e) := by
  let tr (A : Finset L) : Finset L' := univ.filter fun l => e l ∈ A
  let rF (F : Finset (Finset L)) : Finset (Finset L') := (F.image tr).erase ∅
  let rU (T : Finset (Finset L)) : Finset (Finset L') := ((T.image tr).erase ∅).erase univ
  have tr_mono : ∀ {A B}, A ⊆ B → tr A ⊆ tr B :=
    fun hm l hl => mem_filter.2 ⟨mem_univ l, hm (mem_filter.1 hl).2⟩
  have isF : ∀ {F}, IsForest F → IsForest (rF F) := fun hF => by
    refine ⟨fun D hD => nonempty_iff_ne_empty.2 (mem_erase.1 hD).1, fun D hD D' hD' => ?_⟩
    obtain ⟨A, hA, rfl⟩ := mem_image.1 (mem_of_mem_erase hD)
    obtain ⟨B, hB, rfl⟩ := mem_image.1 (mem_of_mem_erase hD')
    exact (hF.2 A hA B hB).imp tr_mono <| Or.imp tr_mono fun hd =>
      disjoint_left.2 fun _ h1 h2 => disjoint_left.1 hd (mem_filter.1 h1).2 (mem_filter.1 h2).2
  have tr_u : ∀ A B, tr (A ∪ B) = tr A ∪ tr B := fun _ _ => by ext; simp [tr]
  have klump : ∀ {F : Finset (Finset L)}, IsForest F → ∀ t G',
      (∑ G, if rF G = G' then kingmanTransition t F G else 0) = kingmanTransition t (rF F) G' := by
    have hgen : ∀ {F : Finset (Finset L)}, IsForest F → ∀ u : Finset (Finset L') → ℝ,
        ∑ G, kingmanGenerator F G * u (rF G) = ∑ G'', kingmanGenerator (rF F) G'' * u G'' := fun {F} hF u => by
      suffices 2 * ∑ G, kingmanGenerator F G * u (rF G) = 2 * ∑ G'', kingmanGenerator (rF F) G'' * u G'' by linarith
      set R := (roots F).filter fun A => tr A ≠ ∅
      have hroots : roots (rF F) = R.image tr := by
        ext D; rw [mem_image]; refine ⟨fun hD => ?_, ?_⟩
        · obtain ⟨hDF, hmax⟩ := mem_roots.1 hD
          obtain ⟨hne, hd⟩ := mem_erase.1 hDF; obtain ⟨A, hA, rfl⟩ := mem_image.1 hd
          obtain ⟨A', hR, hAR⟩ := exists_mem_roots_subset hA
          have hRne : tr A' ≠ ∅ := fun h0 => hne (subset_empty.1 (h0 ▸ tr_mono hAR))
          exact ⟨A', mem_filter.2 ⟨hR, hRne⟩,
            hmax _ (mem_erase.2 ⟨hRne, mem_image_of_mem _ (roots_subset F hR)⟩) (tr_mono hAR)⟩
        · rintro ⟨A, hAf, rfl⟩
          obtain ⟨hA, hne⟩ := mem_filter.1 hAf
          refine mem_roots.2 ⟨mem_erase.2 ⟨hne, mem_image_of_mem _ (roots_subset F hA)⟩, fun D hD hAD => ?_⟩
          obtain ⟨B, hB, rfl⟩ := mem_image.1 (mem_of_mem_erase hD)
          obtain ⟨A', hR, hBR⟩ := exists_mem_roots_subset hB
          obtain ⟨l, hl⟩ := nonempty_iff_ne_empty.2 hne
          obtain rfl := hF.eq_of_mem_roots_of_mem hA hR (mem_filter.1 hl).2 (hBR (mem_filter.1 (hAD hl)).2)
          exact Subset.antisymm (tr_mono hBR) hAD
      have hkg : ∀ {M : Type v} [Fintype M] [DecidableEq M] {G : Finset (Finset M)}, IsForest G →
          ∀ v : Finset (Finset M) → ℝ, 2 * ∑ H, kingmanGenerator G H * v H =
            ∑ p ∈ (roots G).offDiag, (v (insert (p.1 ∪ p.2) G) - v G) := fun {M _ _ G} hG v => by
        rw [hG.sum_kingmanGenerator_mul, mul_add, hG.two_mul_sum_merges, sum_sub_distrib, sum_const, nsmul_eq_mul]
        have h1 := hG.two_mul_sum_merges fun _ => 1
        simp only [sum_const, nsmul_eq_mul, mul_one, hG.card_merges] at h1
        rw [show 2 * (-((#(roots G)).choose 2 : ℝ) * v G) = -(2 * (#(roots G)).choose 2) * v G by ring, h1]; ring
      rw [hkg hF, hkg (isF hF), hroots]
      have hsub : ∑ p ∈ (roots F).offDiag,
          (u (rF (insert (p.1 ∪ p.2) F)) - u (rF F)) =
        ∑ p ∈ R.offDiag, (u (insert (tr p.1 ∪ tr p.2) (rF F)) - u (rF F)) := by
        rw [← sum_subset (offDiag_mono (filter_subset (fun A => tr A ≠ ∅) (roots F)))]
        · refine sum_congr rfl fun ⟨A, B⟩ hp => ?_
          have hne : tr A ∪ tr B ≠ ∅ := fun hc => (mem_filter.1 (mem_offDiag.1 hp).1).2 (union_eq_empty.1 hc).1
          dsimp only [rF]; rw [image_insert, tr_u, erase_insert_of_ne hne]
        · rintro ⟨A, B⟩ hp hnot
          obtain ⟨hA, hB, hAB⟩ : A ∈ roots F ∧ B ∈ roots F ∧ A ≠ B := mem_offDiag.1 hp
          have h0 : tr A = ∅ ∨ tr B = ∅ := by
            by_contra hc; exact hnot (mem_offDiag.2 ⟨mem_filter.2 ⟨hA, (not_or.1 hc).1⟩,
              mem_filter.2 ⟨hB, (not_or.1 hc).2⟩, hAB⟩)
          suffices rF (insert (A ∪ B) F) = rF F by rw [this, sub_self]
          dsimp only [rF]; rw [image_insert, tr_u]
          rcases h0 with h0 | h0
          · rw [h0, empty_union, insert_eq_of_mem (mem_image_of_mem _ (roots_subset F hB))]
          · rw [h0, union_empty, insert_eq_of_mem (mem_image_of_mem _ (roots_subset F hA))]
      rw [hsub]
      have hinj : Set.InjOn tr R := fun A hA B hB heq => by
        obtain ⟨l, hl⟩ := nonempty_iff_ne_empty.2 (mem_filter.1 hA).2
        have hlB : l ∈ tr B := heq ▸ hl
        exact hF.eq_of_mem_roots_of_mem (mem_filter.1 hA).1 (mem_filter.1 hB).1
          (mem_filter.1 hl).2 (mem_filter.1 hlB).2
      exact sum_nbij (Prod.map tr tr)
        (fun ⟨A, B⟩ hp => mem_offDiag.2 ⟨mem_image_of_mem _ (mem_offDiag.1 hp).1,
          mem_image_of_mem _ (mem_offDiag.1 hp).2.1,
          mt (hinj (mem_offDiag.1 hp).1 (mem_offDiag.1 hp).2.1) (mem_offDiag.1 hp).2.2⟩)
        (fun ⟨A₁, B₁⟩ h1 ⟨A₂, B₂⟩ h2 hp => Prod.ext
          (hinj (mem_offDiag.1 h1).1 (mem_offDiag.1 h2).1 (Prod.mk.inj hp).1)
          (hinj (mem_offDiag.1 h1).2.1 (mem_offDiag.1 h2).2.1 (Prod.mk.inj hp).2))
        (fun ⟨D₁, D₂⟩ hp => by
          obtain ⟨⟨A, hA, rfl⟩, ⟨B, hB, rfl⟩, hne⟩ := by simpa [mem_offDiag] using hp
          exact ⟨(A, B), mem_offDiag.2 ⟨hA, hB, fun e' => hne (congrArg tr e')⟩, rfl⟩)
        (fun _ _ => rfl)
    have hpow : ∀ (n : ℕ) {F : Finset (Finset L)}, IsForest F → ∀ w : Finset (Finset L') → ℝ,
        ∑ G, (kingmanGenerator ^ n) F G * w (rF G) = ∑ G'', (kingmanGenerator ^ n) (rF F) G'' * w G'' := by
      intro n; induction n with
      | zero => intro _ _ _; simp [Matrix.one_apply]
      | succ n ih =>
        intro F hF w
        set u : Finset (Finset L') → ℝ := fun H' => ∑ G'', (kingmanGenerator ^ n) H' G'' * w G''
        calc ∑ G, (kingmanGenerator ^ (n + 1)) F G * w (rF G)
            = ∑ H, kingmanGenerator F H * ∑ G, (kingmanGenerator ^ n) H G * w (rF G) := by
              simp_rw [pow_succ', Matrix.mul_apply, sum_mul]; rw [sum_comm]; simp_rw [mul_sum, mul_assoc]
          _ = ∑ H, kingmanGenerator F H * u (rF H) := sum_congr rfl fun H _ => by
              by_cases hQ : kingmanGenerator F H = 0; · simp [hQ]
              refine congrArg (_ * ·) (ih ?_ w)
              simp only [kingmanGenerator, ← mem_merges] at hQ
              split_ifs at hQ with h1 h2; exacts [h1 ▸ hF, (hF.of_mem_merges h2).1, absurd rfl hQ]
          _ = ∑ H', kingmanGenerator (rF F) H' * u H' := hgen hF u
          _ = ∑ G'', (kingmanGenerator ^ (n + 1)) (rF F) G'' * w G'' := by
              simp_rw [u, pow_succ', Matrix.mul_apply, sum_mul, mul_sum, mul_assoc]; rw [sum_comm]
    intro F hF t G'
    simpa [kingmanTransition, mul_ite, mul_one, mul_zero, sum_ite_eq'] using
      (hasSum_sum (s := univ) fun G _ => (hasSum_exp_apply (t • kingmanGenerator) F G).mul_right
        (if rF G = G' then (1 : ℝ) else 0)).unique
      ((hasSum_sum (s := univ) fun G'' _ => (hasSum_exp_apply (t • kingmanGenerator) (rF F) G'').mul_right
        (if G'' = G' then (1 : ℝ) else 0)).congr_fun fun n => by
        simp_rw [smul_pow, Matrix.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum]
        rw [hpow n hF (fun G'' => if G'' = G' then 1 else 0)])
  have hru : ∀ F₁ F₂, rF (F₁ ∪ F₂) = rF F₁ ∪ rF F₂ := fun F₁ F₂ => by
    ext D; simp only [rF, mem_erase, mem_image, mem_union, or_and_right, exists_or, and_or_left]
  have hunr : ∀ G, unroot (rF G) = rU (unroot G) := fun G => by
    have tc : ∀ A, (tr A)ᶜ = tr Aᶜ := fun _ => by ext; simp [tr]
    have tu : tr (univ : Finset L) = univ := filter_true_of_mem fun _ _ => mem_univ _
    ext D; simp only [mem_unroot, rF, rU, mem_erase, mem_image]
    refine ⟨?_, fun ⟨hDu, hD0, B, hB, eB⟩ => ?_⟩
    · rintro (⟨⟨hD0, A, hA, rfl⟩, hDu⟩ | ⟨⟨hDc0, A, hA, hAD⟩, hDu⟩)
      · exact ⟨hDu, hD0, A, Or.inl ⟨hA, fun hc => hDu (hc ▸ tu)⟩, rfl⟩
      · exact ⟨fun hc => hDc0 (hc ▸ compl_univ), fun hc => hDu (hc ▸ compl_empty), Aᶜ,
          Or.inr ⟨by rwa [compl_compl], fun hc => hDu (hAD ▸ compl_compl A ▸ hc ▸ tu)⟩,
          by rw [← tc, hAD, compl_compl]⟩
    · subst eB; rcases hB with ⟨hBG, -⟩ | ⟨hBcG, -⟩
      · exact Or.inl ⟨⟨hD0, B, hBG, rfl⟩, hDu⟩
      · exact Or.inr ⟨⟨mt (compl_eq_empty_iff _).1 hDu, Bᶜ, hBcG, (tc B).symm⟩, mt (compl_eq_univ_iff _).1 hD0⟩
  have key : ∀ (τ : SpeciesTree X) T',
      τ.unrootedDist (s ∘ e) T' = ∑ T, if rU T = T' then τ.unrootedDist s T else 0 := fun τ T' => by
    have hfde : ∀ {A : Finset X}, A ∈ τ.clusters → ∀ G',
        forestDist τ.clusters τ.length (s ∘ e) A G' =
          ∑ G, if rF G = G' then forestDist τ.clusters τ.length s A G else 0 := by
      intro A; induction A using Finset.strongInduction with
      | H A ih =>
      intro hA G'
      have hent : ∀ F', enteringDist τ.clusters τ.length (s ∘ e) A F' =
          ∑ F, if rF F = F' then enteringDist τ.clusters τ.length s A F else 0 := fun F' => by
        simp only [enteringDist, csum, mul_ite, mul_one, mul_zero]
        rw [marg_sum_ite_comp (fun f : childClusters τ.clusters A → Finset (Finset L) =>
          univ.sup f ∪ sampledForest s A) rF]
        simp_rw [show ∀ f' : childClusters τ.clusters A → Finset (Finset L'),
            ∏ B : childClusters τ.clusters A, forestDist τ.clusters τ.length (s ∘ e) B (f' B) =
              ∑ f : childClusters τ.clusters A → Finset (Finset L),
                if (fun B => rF (f B)) = f' then
                  ∏ B : childClusters τ.clusters A, forestDist τ.clusters τ.length s B (f B) else 0 from fun f' => by
          rw [prod_congr rfl fun B _ => ih B.1 (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1 (f' B), Fintype.prod_sum]
          exact sum_congr rfl fun f _ => by rw [prod_ite_zero]; simp [funext_iff]]
        rw [marg_sum_ite_comp (fun f : childClusters τ.clusters A → Finset (Finset L) => fun B => rF (f B))
          (fun f' => univ.sup f' ∪ sampledForest (s ∘ e) A)]
        refine sum_congr rfl fun f _ => ?_
        rw [hru, apply_sup_eq_sup_comp rF hru (by simp [rF]), show rF (sampledForest s A) = sampledForest (s ∘ e) A by
          ext D; simp only [rF, mem_erase, mem_image, mem_sampledForest, Function.comp_apply]
          constructor
          · rintro ⟨hne, _, ⟨l, hl, rfl⟩, rfl⟩
            obtain ⟨l', hl'⟩ := nonempty_iff_ne_empty.2 hne
            obtain rfl : e l' = l := mem_singleton.1 (mem_filter.1 hl').2
            exact ⟨l', hl, by ext; simp [tr, e.injective.eq_iff, eq_comm]⟩
          · rintro ⟨l', hl', rfl⟩
            exact ⟨singleton_ne_empty _, {e l'}, ⟨e l', hl', rfl⟩, by ext; simp [tr, e.injective.eq_iff]⟩]; rfl
      have hK : ∀ F, enteringDist τ.clusters τ.length s A F *
          ∑ G, (if rF G = G' then populationKernel τ.length A F G else 0) =
          enteringDist τ.clusters τ.length s A F * populationKernel τ.length A (rF F) G' := fun F => by
        by_cases h0 : enteringDist τ.clusters τ.length s A F = 0; · simp [h0]
        have hFf := (enteringDist_support τ.isHierarchy τ.length s h0).1
        refine congrArg (_ * ·) ?_
        unfold populationKernel; split_ifs
        · have h1 : Filter.Tendsto (fun t => ∑ G, if rF G = G' then kingmanTransition t F G else 0)
              Filter.atTop (nhds (∑ G, if rF G = G' then kingmanAbsorption F G else 0)) :=
            tendsto_finsetSum univ fun G _ => by split_ifs; exacts [tendsto_kingmanTransition hFf G, tendsto_const_nhds]
          simp_rw [klump hFf] at h1
          exact tendsto_nhds_unique h1 (tendsto_kingmanTransition (isF hFf) G')
        · exact klump hFf _ G'
      rw [forestDist_eq_sum_entering]
      simp_rw [hent, sum_mul, ite_mul, zero_mul]
      rw [sum_comm]; simp_rw [sum_ite_eq, ite_eq_left (mem_univ _), ← hK, mul_sum, mul_ite, mul_zero]
      exact sum_comm.trans (sum_congr rfl fun G _ => by rw [forestDist_eq_sum_entering _ _ s A G]; split_ifs <;> simp)
    unfold SpeciesTree.unrootedDist
    simp_rw [show ∀ G', τ.rootedDist (s ∘ e) G' = ∑ G, if rF G = G' then τ.rootedDist s G else 0 from hfde τ.univ_mem]
    rw [marg_sum_ite_comp rF unroot (τ.rootedDist s) T', marg_sum_ite_comp unroot rU (τ.rootedDist s) T']
    simp_rw [hunr]
  ext T'; rw [key, key, h]

omit [Fintype X] in
theorem subtype_nonempty_iff {S A : Finset X} :
    (A.subtype (· ∈ S)).Nonempty ↔ (A ∩ S).Nonempty :=
  ⟨fun ⟨x, hx⟩ => ⟨x, mem_inter.2 ⟨mem_subtype.1 hx, x.2⟩⟩,
    fun ⟨x, hx⟩ => ⟨⟨x, (mem_inter.1 hx).2⟩, mem_subtype.2 (mem_inter.1 hx).1⟩⟩

theorem unrootedDist_restrict_eq {σ σ' : SpeciesTree X}
    (h : σ.unrootedDist id = σ'.unrootedDist id) (S : Finset X) (hS : S.Nonempty) :
    (σ.restrict S hS).unrootedDist id = (σ'.restrict S hS).unrootedDist id := by
  have key : ∀ τ : SpeciesTree X, (τ.restrict S hS).unrootedDist id = τ.unrootedDist Subtype.val :=
    fun τ => funext fun T' => by
    have hH := τ.isHierarchy
    have hH' := (τ.restrict S hS).isHierarchy
    let s : S → X := Subtype.val
    let chainLen : Finset X → ℝ := fun A =>
      ∑ A' ∈ τ.clusters with A' ⊂ A ∧ A'.subtype (· ∈ S) = A.subtype (· ∈ S), τ.length A'
    have hsmem : ∀ {A B : Finset X}, A ∈ τ.clusters → B ∈ childClusters τ.clusters A →
        (B ∩ S).Nonempty → B.subtype (· ∈ S) ≠ A.subtype (· ∈ S) →
        B.subtype (· ∈ S) ∈ childClusters (restrictClusters S τ.clusters) (A.subtype (· ∈ S)) :=
      fun {A B} hA hB hBS hne => by
        obtain ⟨hBH, hBA, hBmax⟩ := mem_childClusters.1 hB
        refine mem_childClusters.2 ⟨mem_image.2 ⟨B, mem_filter.2 ⟨hBH, hBS⟩, rfl⟩,
          (subtype_mono hBA.subset).ssubset_of_ne hne, fun E' hE' hBE' hE'A => ?_⟩
        obtain ⟨E, hEf, rfl⟩ := mem_image.1 hE'; obtain ⟨hE, -⟩ := mem_filter.1 hEf
        obtain ⟨x, hx⟩ := subtype_nonempty_iff.2 hBS
        have hxB := mem_subtype.1 hx; have hxE := mem_subtype.1 (hBE'.subset hx)
        rcases hH.subset_or_subset_of_mem hE hA hxE (hBA.subset hxB) with hEA | hAE
        · rcases hH.subset_or_subset_of_mem hE hBH hxE hxB with hEB | hBE
          · exact not_subset_of_ssubset hBE' (subtype_mono hEB)
          · exact hBmax E hE (hBE.ssubset_of_ne fun e => lt_irrefl _ (e ▸ hBE'))
              (hEA.ssubset_of_ne fun e => lt_irrefl _ (e ▸ hE'A))
        · exact not_subset_of_ssubset hE'A (subtype_mono hAE)
    have hempty : ∀ {B : Finset X}, B ∈ τ.clusters → (∀ l : S, s l ∉ B) → ∀ G,
        forestDist τ.clusters τ.length s B G = if G = ∅ then 1 else 0 := fun {B} hB hs G => by
      have hz : ∀ G, G ≠ ∅ → forestDist τ.clusters τ.length s B G = 0 := fun G hG => by
        by_contra h0
        obtain ⟨hGf, -, hlin⟩ := forestDist_support hH τ.length s hB h0
        obtain ⟨C, hC⟩ := nonempty_iff_ne_empty.2 hG
        obtain ⟨l, hl⟩ := hGf.1 C hC
        have hl' := subset_lineages hC hl; rw [hlin, mem_filter] at hl'
        exact hs l hl'.2
      split_ifs with hG
      · subst hG; have hsum := forestDist_sum hH τ.length s hB
        rwa [← sum_erase_add _ _ (mem_univ ∅), sum_eq_zero fun G hG => hz G (ne_of_mem_erase hG),
          zero_add] at hsum
      · exact hz G hG
    have hprune : ∀ {A : Finset X}, A ∈ τ.clusters → (A ∩ S).Nonempty → ∀ F,
        enteringDist τ.clusters τ.length s A F =
          ∑ F₀, enteringDist (τ.restrict S hS).clusters (τ.restrict S hS).length id
              (A.subtype (· ∈ S)) F₀ * kingmanTransition (chainLen A) F₀ F := by
      intro A; induction A using Finset.strongInduction with
      | H A ih =>
      intro hA hAS F
      have hB_step : ∀ {B : Finset X}, B ⊂ A → B ∈ τ.clusters → (B ∩ S).Nonempty → ∀ G,
          forestDist τ.clusters τ.length s B G =
            ∑ F₀, enteringDist (τ.restrict S hS).clusters (τ.restrict S hS).length id
                (B.subtype (· ∈ S)) F₀ * kingmanTransition (chainLen B + τ.length B) F₀ G := by
        intro B hBA hBH hBS G
        have hBu : B ≠ univ := fun h => not_subset_of_ssubset (h ▸ hBA) (subset_univ A)
        rw [forestDist_eq_sum_entering, populationKernel_ne_univ _ hBu]
        simp_rw [ih B hBA hBH hBS, sum_mul]; rw [sum_comm]
        refine sum_congr rfl fun F₀ _ => ?_
        rw [kingmanTransition_add, Matrix.mul_apply, mul_sum]
        exact sum_congr rfl fun _ _ => by ring
      by_cases hc : ∃ B₀ ∈ childClusters τ.clusters A, B₀.subtype (· ∈ S) = A.subtype (· ∈ S)
      · obtain ⟨B₀, hB₀, htr⟩ := hc
        obtain ⟨hB₀H, hB₀A, -⟩ := mem_childClusters.1 hB₀
        have hB₀S : (B₀ ∩ S).Nonempty := subtype_nonempty_iff.1 (htr ▸ subtype_nonempty_iff.2 hAS)
        have hmem : ∀ {l : S}, s l ∈ A → s l ∈ B₀ := fun {l} hm =>
          mem_subtype.1 (htr ▸ (mem_subtype.2 hm : l ∈ A.subtype (· ∈ S)))
        have hchain : enteringDist τ.clusters τ.length s A F = forestDist τ.clusters τ.length s B₀ F := by
          rw [enteringDist, csum_filter (· = B₀) (fun B hB hne => hempty (mem_childClusters.1 hB).1
              fun l hl => disjoint_left.1 (hH.disjoint_of_mem_childClusters hB hB₀ hne) hl
                (hmem ((mem_childClusters.1 hB).2.1.subset hl))),
            filter_eq', ite_eq_left hB₀, csum_singleton, show sampledForest s A = sampledForest s B₀ by
              unfold sampledForest; congr 1; ext l
              exact ⟨fun h => mem_filter.2 ⟨mem_univ _, hmem (mem_filter.1 h).2⟩,
                fun h => mem_filter.2 ⟨mem_univ _, hB₀A.subset (mem_filter.1 h).2⟩⟩]
          refine (sum_congr rfl fun x _ => show _ = if x = F then forestDist τ.clusters τ.length s B₀ x else 0 by
            by_cases h0 : forestDist τ.clusters τ.length s B₀ x = 0; · simp [h0]
            rw [union_eq_left.2 (forestDist_support hH τ.length s hB₀H h0).2.1]; split_ifs <;> ring).trans
            (by rw [sum_ite_eq']; simp)
        rw [hchain, hB_step hB₀A hB₀H hB₀S F, htr]
        have hset : τ.clusters.filter (fun A' => A' ⊂ A ∧ A'.subtype (· ∈ S) = A.subtype (· ∈ S)) =
            insert B₀ (τ.clusters.filter (fun A' => A' ⊂ B₀ ∧ A'.subtype (· ∈ S) = B₀.subtype (· ∈ S))) := by
          ext A'; simp only [mem_insert, mem_filter]; constructor
          · rintro ⟨hA'H, hA'A, htr'⟩
            obtain ⟨B, hB, hA'B⟩ := hH.exists_mem_childClusters_superset hA'H hA'A
            obtain ⟨x, hx⟩ := subtype_nonempty_iff.2 hAS
            obtain rfl : B = B₀ := by
              by_contra hne
              exact disjoint_left.1 (hH.disjoint_of_mem_childClusters hB hB₀ hne)
                (hA'B (mem_subtype.1 (htr'.symm ▸ hx))) (mem_subtype.1 (htr.symm ▸ hx))
            exact hA'B.eq_or_ssubset.imp id fun hs' => ⟨hA'H, hs', htr'.trans htr.symm⟩
          · rintro (rfl | ⟨hA'H, hA'B₀, htr'⟩)
            · exact ⟨hB₀H, hB₀A, htr⟩
            · exact ⟨hA'H, hA'B₀.trans hB₀A, htr'.trans htr⟩
        rw [show chainLen B₀ + τ.length B₀ = chainLen A by
          dsimp only [chainLen]; rw [hset, sum_insert (fun hm => lt_irrefl _ (mem_filter.1 hm).2.1), add_comm]]
      · push Not at hc
        have hcl0 : chainLen A = 0 := sum_eq_zero fun A' hA' => by
          obtain ⟨hA'H, hA'A, htr'⟩ := mem_filter.1 hA'
          obtain ⟨B, hB, hA'B⟩ := hH.exists_mem_childClusters_superset hA'H hA'A
          exact absurd (Subset.antisymm (subtype_mono (mem_childClusters.1 hB).2.1.subset)
            (htr' ▸ subtype_mono hA'B)) (hc B hB)
        simp only [hcl0, kingmanTransition_zero, Matrix.one_apply, mul_ite, mul_one, mul_zero,
          sum_ite_eq', mem_univ, ite_true]
        unfold enteringDist
        rw [show sampledForest s A = sampledForest id (A.subtype (· ∈ S)) by
            unfold sampledForest; congr 1; ext l; simp [s, mem_subtype],
          csum_filter (fun B => (B ∩ S).Nonempty) fun B hB hBS =>
            hempty (mem_childClusters.1 hB).1 fun l hl => hBS ⟨l, mem_inter.2 ⟨hl, l.2⟩⟩]
        let e : ((childClusters τ.clusters A).filter fun B => (B ∩ S).Nonempty) ≃
            childClusters (τ.restrict S hS).clusters (A.subtype (· ∈ S)) :=
          Equiv.ofBijective (fun B => ⟨B.1.subtype (· ∈ S),
              hsmem hA (mem_filter.1 B.2).1 (mem_filter.1 B.2).2 (hc B.1 (mem_filter.1 B.2).1)⟩)
            ⟨fun B₁ B₂ he => Subtype.ext <| by
              have he' : B₁.1.subtype (· ∈ S) = B₂.1.subtype (· ∈ S) := congrArg Subtype.val he
              by_contra hne; obtain ⟨x, hx⟩ := subtype_nonempty_iff.2 (mem_filter.1 B₁.2).2
              exact disjoint_left.1 (hH.disjoint_of_mem_childClusters (mem_filter.1 B₁.2).1 (mem_filter.1 B₂.2).1 hne)
                (mem_subtype.1 hx) (mem_subtype.1 (he' ▸ hx)),
             fun D => by
              obtain ⟨hDH, hDA, -⟩ := mem_childClusters.1 D.2
              obtain ⟨x, hx⟩ := hH'.2.2.1 D.1 hDH; obtain ⟨y, hyA, hyD⟩ := exists_of_ssubset hDA
              obtain ⟨B, hB, hxB⟩ := hH.exists_mem_childClusters
                (one_lt_card.2 ⟨x, mem_subtype.1 (hDA.subset hx), y, mem_subtype.1 hyA,
                  fun e => hyD (Subtype.ext e ▸ hx)⟩) (mem_subtype.1 (hDA.subset hx))
              have hBS : (B ∩ S).Nonempty := ⟨x, mem_inter.2 ⟨hxB, x.2⟩⟩
              refine ⟨⟨B, mem_filter.2 ⟨hB, hBS⟩⟩, Subtype.ext ?_⟩
              by_contra hne
              exact disjoint_left.1 (hH'.disjoint_of_mem_childClusters
                (hsmem hA hB hBS (hc B hB)) D.2 hne) (mem_subtype.2 hxB) hx⟩
        refine csum_equiv e (fun ⟨B, hBf⟩ => funext fun G => ?_) _
        obtain ⟨hB, hBS⟩ := mem_filter.1 hBf
        obtain ⟨hBH, hBA, hBmax⟩ := mem_childClusters.1 hB
        have hBc := hsmem hA hB hBS (hc B hB)
        have hBu : B.subtype (· ∈ S) ≠ univ :=
          fun he => not_subset_of_ssubset (he ▸ (mem_childClusters.1 hBc).2.1) (subset_univ _)
        have hlen : chainLen B + τ.length B = (τ.restrict S hS).length (B.subtype (· ∈ S)) := by
          show chainLen B + τ.length B = τ.restrictLength S (B.subtype (· ∈ S))
          dsimp only [chainLen]; unfold SpeciesTree.restrictLength
          have hset : τ.clusters.filter (fun A' => A' ≠ univ ∧ A'.subtype (· ∈ S) = B.subtype (· ∈ S)) =
              insert B (τ.clusters.filter (fun A' => A' ⊂ B ∧ A'.subtype (· ∈ S) = B.subtype (· ∈ S))) := by
            ext A'; simp only [mem_insert, mem_filter]; constructor
            · rintro ⟨hA'H, -, htr⟩
              obtain ⟨x, hx⟩ := subtype_nonempty_iff.2 hBS
              have hxB := mem_subtype.1 hx; have hxA' := mem_subtype.1 (htr.symm ▸ hx)
              rcases hH.subset_or_subset_of_mem hA'H hBH hxA' hxB with hs' | hBA'
              · exact hs'.eq_or_ssubset.imp id fun hlt => ⟨hA'H, hlt, htr⟩
              · refine Or.inl ((hBA'.eq_or_ssubset.resolve_right fun hlt => ?_).symm)
                rcases hH.subset_or_subset_of_mem hA'H hA hxA' (hBA.subset hxB) with hA'A | hAA'
                · exact hA'A.eq_or_ssubset.elim (fun e => hc B hB (e ▸ htr).symm) (hBmax A' hA'H hlt)
                · exact hc B hB (Subset.antisymm (subtype_mono hBA.subset) (htr ▸ subtype_mono hAA'))
            · rintro (rfl | ⟨hA'H, hA'B, htr⟩)
              · exact ⟨hBH, fun e => not_subset_of_ssubset (e ▸ hBA) (subset_univ A), rfl⟩
              · exact ⟨hA'H, fun e => not_subset_of_ssubset (e ▸ hA'B.trans hBA) (subset_univ A), htr⟩
          rw [hset, sum_insert (fun hm => lt_irrefl _ (mem_filter.1 hm).2.1), add_comm]
        change _ = forestDist (τ.restrict S hS).clusters (τ.restrict S hS).length id (B.subtype (· ∈ S)) G
        rw [hB_step hBA hBH hBS G, hlen, forestDist_eq_sum_entering, populationKernel_ne_univ _ hBu]
    have hrd : ∀ G, (τ.restrict S hS).rootedDist id G = τ.rootedDist s G := fun G => by
      unfold SpeciesTree.rootedDist
      rw [forestDist_eq_sum_entering, forestDist_eq_sum_entering, populationKernel_univ, populationKernel_univ]
      simp_rw [hprune τ.univ_mem (by simpa using hS),
        show (univ : Finset X).subtype (· ∈ S) = univ by ext; simp, sum_mul]
      rw [sum_comm]; symm; refine sum_congr rfl fun F₀ _ => ?_
      by_cases h0 : enteringDist (τ.restrict S hS).clusters (τ.restrict S hS).length id univ F₀ = 0
      · simp only [h0, zero_mul, sum_const_zero]
      · simp_rw [mul_assoc, ← mul_sum]
        have hF₀ := (enteringDist_support hH' _ id h0).1
        rw [show ∑ F', kingmanTransition (chainLen univ) F₀ F' * kingmanAbsorption F' G = kingmanAbsorption F₀ G by
          refine tendsto_nhds_unique (tendsto_finsetSum _ fun F' _ => ?_)
            (((tendsto_kingmanTransition hF₀ G).comp
              (Filter.tendsto_atTop_add_const_left Filter.atTop (chainLen univ) Filter.tendsto_id)).congr fun t => by
              rw [Function.comp_apply, kingmanTransition_add, Matrix.mul_apply])
          by_cases hkt0 : kingmanTransition (chainLen univ) F₀ F' = 0
          · simp [hkt0]
          · rw [kingmanTransition_apply hF₀] at hkt0
            exact (tendsto_kingmanTransition
              (jumpMatrix_pow_support hF₀ (right_ne_zero_of_mul hkt0)).1 G).const_mul _]
    unfold SpeciesTree.unrootedDist; simp_rw [hrd]; rfl
  rw [key, key]; exact unrootedDist_comp_eq h (Function.Embedding.subtype (· ∈ S))

end ADR11
