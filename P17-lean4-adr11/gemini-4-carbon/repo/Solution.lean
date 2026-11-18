module

public import ADR11.Nonbinary.FiveTaxa

@[expose] public section

namespace ADR11.Challenge

open ADR11 Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem unrootedDist_nonneg {L : Type*} [Fintype L] [DecidableEq L] (σ : SpeciesTree X)
    (s : L → X) (T : Finset (Finset L)) : 0 ≤ σ.unrootedDist s T := ADR11.unrootedDist_nonneg σ s T

theorem unrootedDist_sum {L : Type*} [Fintype L] [DecidableEq L] (σ : SpeciesTree X)
    (s : L → X) : ∑ T, σ.unrootedDist s T = 1 := ADR11.unrootedDist_sum σ s

theorem fourTaxa_balanced (σ : SpeciesTree (Fin 4))
    (hσ : σ.clusters = {univ, {0, 1}, {2, 3}, {0}, {1}, {2}, {3}}) :
    σ.unrootedDist id {{0, 1}, {2, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 - 2 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3})) ∧
    σ.unrootedDist id {{0, 2}, {1, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3})) ∧
    σ.unrootedDist id {{0, 3}, {1, 2}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3})) := by
  obtain ⟨e1, e2, e3⟩ := n4_quartets_U4 σ (Or.inr rfl) (by rw [hσ]; decide)
  simp only [↓reduceIte] at e1 e2 e3
  rw [unrootedLength_01, ite_eq_left (by rw [hσ]; decide), ite_eq_left (by rw [hσ]; decide)] at e1 e2 e3
  refine ⟨?_, ?_, ?_⟩ <;> [convert e1 using 2; convert e2 using 2; convert e3 using 2] <;> decide +kernel

theorem fourTaxa_caterpillar (σ : SpeciesTree (Fin 4))
    (hσ : σ.clusters = {univ, {0, 1}, {0, 1, 2}, {0}, {1}, {2}, {3}}) :
    σ.unrootedDist id {{0, 1}, {2, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 - 2 / 3 * exp (-σ.length {0, 1}) ∧
    σ.unrootedDist id {{0, 2}, {1, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 / 3 * exp (-σ.length {0, 1}) ∧
    σ.unrootedDist id {{0, 3}, {1, 2}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 / 3 * exp (-σ.length {0, 1}) := by
  obtain ⟨e1, e2, e3⟩ := n4_quartets_U4 σ (Or.inr rfl) (by rw [hσ]; decide)
  simp only [↓reduceIte] at e1 e2 e3
  rw [unrootedLength_01, ite_eq_left (by rw [hσ]; decide), ite_eq_right (by rw [hσ]; decide), add_zero] at e1 e2 e3
  refine ⟨?_, ?_, ?_⟩ <;> [convert e1 using 2; convert e2 using 2; convert e3 using 2] <;> decide +kernel

theorem proposition11_theorem9 (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameRootedMetricTree σ' := by
  have cne : ∀ {A : Finset X}, A ≠ univ → Aᶜ.Nonempty := fun hAu =>
    let ⟨x, hx⟩ := not_forall.1 (mt eq_univ_iff_forall.2 hAu); ⟨x, mem_compl.2 hx⟩
  have ex5 : ∀ u v w : X, ∃ S : Finset X, {u, v, w} ⊆ S ∧ #S = 5 := fun u v w =>
    let ⟨S, hTS, _, hS⟩ := exists_subsuperset_card_eq (subset_univ {u, v, w})
      (card_le_three.trans (by decide)) (by rwa [card_univ])
    ⟨S, hTS, hS⟩
  have eq_cc : ∀ {τ : SpeciesTree X} {R R'}, R ∈ childClusters τ.clusters univ →
      R' ∈ childClusters τ.clusters univ → ∀ {x}, x ∈ R → x ∈ R' → R = R' :=
    fun {τ _ _} hR hR' {_} hx hx' => by
      by_contra hne; exact disjoint_left.1 (τ.isHierarchy.disjoint_of_mem_childClusters hR hR' hne) hx hx'
  have mc_res : ∀ (τ : SpeciesTree X) {S : Finset X} (hS : S.Nonempty) {R₀}
      (hR₀ : R₀ ∈ childClusters τ.clusters univ) {u w} (huR : u ∈ R₀) (huS : u ∈ S)
      (hwR : w ∉ R₀) (hwS : w ∈ S) {C : Finset S},
      C ∈ childClusters (τ.restrict S hS).clusters univ ↔
        ∃ R ∈ childClusters τ.clusters univ, (R ∩ S).Nonempty ∧ R.subtype (· ∈ S) = C := by
    intro τ S hS R₀ hR₀ u w huR huS hwR hwS C
    have hH := τ.isHierarchy
    have htr : ∀ R ∈ childClusters τ.clusters univ, (R ∩ S).Nonempty →
        R.subtype (· ∈ S) ∈ (τ.restrict S hS).clusters ∧ R.subtype (· ∈ S) ⊂ univ := by
      intro R hR hRS
      obtain ⟨y, hyS, hyR⟩ := not_subset.1 fun hSR => hwR (eq_cc hR₀ hR huR (hSR huS) ▸ hSR hwS)
      exact ⟨subtype_mem_restrictClusters (mem_childClusters.1 hR).1 hRS,
        ssubset_univ_iff.2 (subtype_ne_univ_iff.2 ⟨y, mem_inter.2 ⟨mem_compl.2 hyR, hyS⟩⟩)⟩
    have hsup : ∀ B ∈ τ.clusters, B ≠ univ → ∃ R ∈ childClusters τ.clusters univ, B ⊆ R :=
      fun B hB hBu => hH.exists_mem_childClusters_superset hB (ssubset_univ_iff.2 hBu)
    refine ⟨fun hC => ?_, ?_⟩
    · obtain ⟨hCcl, hCu, hmax⟩ := mem_childClusters.1 hC
      obtain ⟨B, hB, ⟨y, hy⟩, rfl⟩ := mem_restrictClusters.1 hCcl
      obtain ⟨R, hR, hBR⟩ := hsup B hB fun e => hCu.ne (e ▸ subtype_univ _)
      have hRS : (R ∩ S).Nonempty := ⟨y, mem_inter.2 ⟨hBR (mem_inter.1 hy).1, (mem_inter.1 hy).2⟩⟩
      obtain ⟨hRcl, hRu⟩ := htr R hR hRS
      exact ⟨R, hR, hRS, ((subtype_mono hBR).eq_or_ssubset.resolve_right fun hs => hmax _ hRcl hs hRu).symm⟩
    · rintro ⟨R, hR, ⟨y, hy⟩, rfl⟩
      obtain ⟨hRcl, hRu⟩ := htr R hR ⟨y, hy⟩
      refine mem_childClusters.2 ⟨hRcl, hRu, fun D hD hRD hDu => ?_⟩
      obtain ⟨B, hB, -, rfl⟩ := mem_restrictClusters.1 hD
      obtain ⟨R', hR', hBR'⟩ := hsup B hB fun e => hDu.ne (e ▸ subtype_univ _)
      have hyB : y ∈ B := mem_subtype.1 (hRD.subset (mem_subtype.2 (mem_inter.1 hy).1 : (⟨y, (mem_inter.1 hy).2⟩ : S) ∈ _))
      obtain rfl := eq_cc hR hR' (mem_inter.1 hy).1 (hBR' hyB)
      exact not_subset_of_ssubset hRD (subtype_mono hBR')
  have mc_iff : ∀ (τ : SpeciesTree X) {A : Finset X}, A ∈ unroot τ.clusters →
      (A ∈ childClusters τ.clusters univ ↔
        ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 → (A ∩ S).Nonempty → (Aᶜ ∩ S).Nonempty →
          A.subtype (· ∈ S) ∈ childClusters (τ.restrict S hS).clusters univ) := fun τ {A} hA => by
    refine ⟨fun hAR S hS _ ⟨y, hy⟩ ⟨z, hz⟩ => (mc_res τ hS hAR (mem_inter.1 hy).1 (mem_inter.1 hy).2
        (mem_compl.1 (mem_inter.1 hz).1) (mem_inter.1 hz).2).2 ⟨A, hAR, ⟨y, hy⟩, rfl⟩,
      fun hall => ?_⟩
    by_contra hAR
    suffices ∃ S : Finset X, ∃ hS : S.Nonempty, #S = 5 ∧ (A ∩ S).Nonempty ∧ (Aᶜ ∩ S).Nonempty ∧
        A.subtype (· ∈ S) ∉ childClusters (τ.restrict S hS).clusters univ by
      obtain ⟨S, hS, hS5, hAS, hAcS, hnot⟩ := this; exact hnot (hall S hS hS5 hAS hAcS)
    obtain ⟨hAne, hAu⟩ := nonempty_of_mem_unroot τ.isHierarchy hA
    have hroot : ∀ x, ∃ R ∈ childClusters τ.clusters univ, x ∈ R :=
      fun x => τ.isHierarchy.exists_mem_childClusters (by rw [card_univ]; omega) (mem_univ x)
    have hother : ∀ {R : Finset X} {ℓ : X}, ℓ ∈ R → R ≠ {ℓ} → ∃ m ∈ R, m ≠ ℓ := fun hℓR hRℓ => by
      by_contra hcon
      exact hRℓ (eq_singleton_iff_unique_mem.2 ⟨hℓR, fun y hy => by by_contra hyℓ; exact hcon ⟨y, hy, hyℓ⟩⟩)
    have tri : ∀ {R : Finset X} (hR : R ∈ childClusters τ.clusters univ) {u v w : X},
        u ∈ A → u ∈ R → v ∉ A → w ∉ R → (v ∈ R ∨ w ∈ A) →
        ∃ S : Finset X, ∃ hS : S.Nonempty, #S = 5 ∧ (A ∩ S).Nonempty ∧ (Aᶜ ∩ S).Nonempty ∧
          A.subtype (· ∈ S) ∉ childClusters (τ.restrict S hS).clusters univ := by
      intro R hR u v w huA huR hvA hwR hbad
      obtain ⟨S, hTS, hS5⟩ := ex5 u v w
      have huS : u ∈ S := hTS (by simp); have hvS : v ∈ S := hTS (by simp); have hwS : w ∈ S := hTS (by simp)
      refine ⟨S, ⟨u, huS⟩, hS5, ⟨u, mem_inter.2 ⟨huA, huS⟩⟩, ⟨v, mem_inter.2 ⟨mem_compl.2 hvA, hvS⟩⟩, fun hC => ?_⟩
      obtain ⟨R', hR', -, heq⟩ := (mc_res τ ⟨u, huS⟩ hR huR huS hwR hwS).1 hC
      obtain rfl := eq_cc hR hR' huR ((mem_iff_of_subtype_eq heq huS).2 huA)
      exact hbad.elim (fun hvR => hvA ((mem_iff_of_subtype_eq heq hvS).1 hvR))
        (fun hwA => hwR ((mem_iff_of_subtype_eq heq hwS).2 hwA))
    by_cases hA1 : #A = 1
    · obtain ⟨ℓ, rfl⟩ := card_eq_one.1 hA1
      obtain ⟨R, hR, hℓR⟩ := hroot ℓ
      obtain ⟨m, hmR, hmℓ⟩ := hother hℓR fun e => hAR (e ▸ hR)
      obtain ⟨r, hr⟩ := cne (mem_childClusters.1 hR).2.1.ne
      exact tri hR (mem_singleton_self ℓ) hℓR (by simpa using hmℓ) (mem_compl.1 hr) (Or.inl hmR)
    by_cases hAc1 : #Aᶜ = 1
    · obtain ⟨ℓ, hℓ⟩ := card_eq_one.1 hAc1
      have hmemA : ∀ y, y ∈ A ↔ y ≠ ℓ := fun y => by
        have : y ∉ A ↔ y = ℓ := by rw [← mem_compl, hℓ, mem_singleton]
        tauto
      have hℓA : ℓ ∉ A := fun h' => (hmemA ℓ).1 h' rfl
      obtain ⟨R, hR, hℓR⟩ := hroot ℓ
      by_cases hRℓ : R = {ℓ}
      · subst hRℓ; obtain ⟨y, hy⟩ := hAne; obtain ⟨R₁, hR₁, hyR₁⟩ := hroot y
        have hℓR₁ : ℓ ∉ R₁ := fun h' => (hmemA y).1 hy (mem_singleton.1
          (eq_cc hR hR₁ (mem_singleton_self ℓ) h' ▸ hyR₁))
        obtain ⟨r₂, hr₂, hr₂R₁⟩ : ∃ r₂, r₂ ≠ ℓ ∧ r₂ ∉ R₁ := by
          by_contra hcon; refine hAR (show A ∈ _ from ?_)
          convert hR₁ using 1; ext z; rw [hmemA]
          exact ⟨fun hz => by by_contra hzR; exact hcon ⟨z, hz, hzR⟩, fun hz e => hℓR₁ (e ▸ hz)⟩
        exact tri hR₁ hy hyR₁ hℓA hr₂R₁ (Or.inr ((hmemA r₂).2 hr₂))
      · obtain ⟨m, hmR, hmℓ⟩ := hother hℓR hRℓ
        obtain ⟨r, hr⟩ := cne (mem_childClusters.1 hR).2.1.ne
        exact tri hR ((hmemA m).2 hmℓ) hmR hℓA (mem_compl.1 hr)
          (Or.inr ((hmemA r).2 fun e => mem_compl.1 hr (e ▸ hℓR)))
    obtain ⟨a, ha, a', ha', b, hb, b', hb', haa, hbb, hQ⟩ :=
      exists_distinguishing_quartet τ hA (by have := card_pos.2 hAne; omega)
        (by have := card_pos.2 (cne hAu); omega)
    rw [mem_compl] at hb hb'
    set Q : Finset X := {a, a', b, b'} with hQdef
    have hQ4 := card_quartet ha ha' hb hb' haa hbb
    obtain ⟨R₀, hR₀, haR₀⟩ := hroot a
    obtain ⟨x, hxQ, z, hzS, hzR₀⟩ : ∃ x ∉ Q, ∃ z ∈ insert x Q, z ∉ R₀ := by
      by_cases hQR : Q ⊆ R₀
      · obtain ⟨x, hx⟩ := cne (mem_childClusters.1 hR₀).2.1.ne
        exact ⟨x, fun hxQ => mem_compl.1 hx (hQR hxQ), x, mem_insert_self _ _, mem_compl.1 hx⟩
      · obtain ⟨z, hzQ, hzR⟩ := not_subset.1 hQR
        obtain ⟨x, hx⟩ : Qᶜ.Nonempty := card_pos.1 (by rw [card_compl, hQdef, hQ4]; omega)
        exact ⟨x, mem_compl.1 hx, z, mem_insert_of_mem hzQ, hzR⟩
    set S : Finset X := insert x Q with hSdef
    have hS : S.Nonempty := insert_nonempty _ _
    refine ⟨S, hS, by rw [hSdef, card_insert_of_notMem hxQ, hQdef, hQ4],
      ⟨a, mem_inter.2 ⟨ha, by simp [hSdef, hQdef]⟩⟩,
      ⟨b, mem_inter.2 ⟨mem_compl.2 hb, by simp [hSdef, hQdef]⟩⟩, fun hC => ?_⟩
    obtain ⟨R', hR', -, hR'eq⟩ := (mc_res τ hS hR₀ haR₀ (by simp [hSdef, hQdef]) hzR₀ hzS).1 hC
    have hmem := fun (y : X) (hy : y ∈ S) => mem_iff_of_subtype_eq hR'eq hy
    have hR'U := mem_unroot.2 (Or.inl ⟨(mem_childClusters.1 hR').1, (mem_childClusters.1 hR').2.1.ne⟩)
    exact hAR (hQ R' hR'U ((hmem a (by simp [hSdef, hQdef])).2 ha) ((hmem a' (by simp [hSdef, hQdef])).2 ha')
      (mt (hmem b (by simp [hSdef, hQdef])).1 hb) (mt (hmem b' (by simp [hSdef, hQdef])).1 hb') ▸ hR')
  have hH := σ.isHierarchy
  have hU := sameUnrootedMetricTree_of_unrootedDist_eq σ σ' h
  have h5 : ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
      (σ.restrict S hS).SameRootedMetricTree (σ'.restrict S hS) :=
    fun S hS hS5 => appC_sameRootedMetricTree (by simpa using hS5) _ _ (unrootedDist_restrict_eq h S hS)
  have key : ∀ τ τ' : SpeciesTree X, unroot τ.clusters = unroot τ'.clusters →
      (∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 → (τ.restrict S hS).clusters = (τ'.restrict S hS).clusters) →
      ∀ A ∈ childClusters τ.clusters univ, A ∈ childClusters τ'.clusters univ := by
    intro τ τ' hU' h5' A hA
    have hAU := mem_unroot.2 (Or.inl ⟨(mem_childClusters.1 hA).1, (mem_childClusters.1 hA).2.1.ne⟩)
    exact (mc_iff τ' (hU' ▸ hAU)).2 fun S hS hS5 hAS hAcS =>
      h5' S hS hS5 ▸ (mc_iff τ hAU).1 hA S hS hS5 hAS hAcS
  have hR : childClusters σ.clusters univ = childClusters σ'.clusters univ := by
    ext A; exact ⟨key σ σ' hU.1 (fun S hS hS5 => (h5 S hS hS5).1) A,
      key σ' σ hU.1.symm (fun S hS hS5 => (h5 S hS hS5).1.symm) A⟩
  have miff : ∀ G : Finset (Finset X), IsHierarchy G → ∀ C,
      C ∈ G ↔ C = univ ∨ (C ∈ unroot G ∧ ∃ R ∈ childClusters G univ, C ⊆ R) := fun G hG C => by
    refine ⟨fun hC => ?_, ?_⟩
    · by_cases hCu : C = univ; · exact Or.inl hCu
      exact Or.inr ⟨mem_unroot.2 (Or.inl ⟨hC, hCu⟩),
        hG.exists_mem_childClusters_superset hC (ssubset_univ_iff.2 hCu)⟩
    · rintro (rfl | ⟨hC, R, hR, hCR⟩); · exact hG.1
      have hRG := (mem_childClusters.1 hR).1
      rcases mem_unroot.1 hC with ⟨hc, -⟩ | ⟨hc, hu⟩; · exact hc
      rcases hG.2.2.2 _ hc R hRG with h' | h' | h'
      · exact absurd (univ_subset_iff.1 (union_compl C ▸ union_subset hCR h')) (mem_childClusters.1 hR).2.1.ne
      · exact absurd (univ_subset_iff.1 (union_compl C ▸ union_subset (hCR.trans h') Subset.rfl)) hu
      · exact compl_inj_iff.1 (Subset.antisymm (subset_compl_iff_disjoint_right.2 h')
          (compl_subset_compl.2 hCR)) ▸ hRG
  have hcl : σ.clusters = σ'.clusters := by
    ext C; rw [miff _ hH, miff _ σ'.isHierarchy, hU.1, hR]
  refine ⟨hcl, fun A hA hA2 hAu => ?_⟩
  by_cases hAc : Aᶜ ∈ σ.clusters
  · have hAr : A ∈ childClusters σ.clusters univ :=
      hH.childClusters_eq_pair hA hAc disjoint_compl_right (union_compl A) ▸ mem_insert_self _ _
    obtain ⟨a₁, ha₁, a₂, ha₂, ha12, hmax⟩ := exists_pair_max σ hA2
    obtain ⟨w', hw'⟩ := cne hAu
    obtain ⟨S, hTS, hS5⟩ := ex5 a₁ a₂ w'
    have ha₁S : a₁ ∈ S := hTS (by simp); have ha₂S : a₂ ∈ S := hTS (by simp); have hw'S : w' ∈ S := hTS (by simp)
    have huniq : ∀ C ∈ σ.clusters, C.subtype (· ∈ S) = A.subtype (· ∈ S) → C = A := fun C hC hCA => by
      have hmem := fun (x : X) (hx : x ∈ S) => mem_iff_of_subtype_eq hCA hx
      have ha₁C := (hmem a₁ ha₁S).2 ha₁; have ha₂C := (hmem a₂ ha₂S).2 ha₂
      have hCu : C ≠ univ := fun e => mem_compl.1 hw' ((hmem w' hw'S).1 (e ▸ mem_univ w'))
      rcases hH.subset_or_subset_of_mem hC hA ha₁C ha₁ with hCB | hAC
      · exact hCB.eq_or_ssubset.resolve_right (hmax C hC ha₁C ha₂C)
      · exact (hAC.eq_or_ssubset.resolve_right fun hlt =>
          (mem_childClusters.1 hAr).2.2 C hC hlt (ssubset_univ_iff.2 hCu)).symm
    have h2 : 2 ≤ #(A.subtype (· ∈ S)) :=
      one_lt_card.2 ⟨⟨a₁, ha₁S⟩, mem_subtype.2 ha₁, ⟨a₂, ha₂S⟩, mem_subtype.2 ha₂,
        fun e => ha12 (congrArg Subtype.val e)⟩
    have hrlen : ∀ τ : SpeciesTree X, A ∈ τ.clusters →
        (∀ B ∈ τ.clusters, B.subtype (· ∈ S) = A.subtype (· ∈ S) → B = A) →
        τ.restrictLength S (A.subtype (· ∈ S)) = τ.length A := fun τ hAt hu =>
      sum_eq_single_of_mem A (mem_filter.2 ⟨hAt, hAu, rfl⟩) fun B hB hBA =>
        absurd (hu B (mem_filter.1 hB).1 (mem_filter.1 hB).2.2) hBA
    have : σ.restrictLength S (A.subtype (· ∈ S)) = σ'.restrictLength S (A.subtype (· ∈ S)) :=
      (h5 S ⟨a₁, ha₁S⟩ hS5).2 _ (subtype_mem_restrictClusters hA ⟨a₁, mem_inter.2 ⟨ha₁, ha₁S⟩⟩)
        h2 (subtype_ne_univ_iff.2 ⟨w', mem_inter.2 ⟨hw', hw'S⟩⟩)
    rwa [hrlen σ hA huniq, hrlen σ' (hcl ▸ hA) fun C hC => huniq C (hcl ▸ hC)] at this
  · have hAc2 : 2 ≤ #Aᶜ := by
      by_contra hlt
      obtain ⟨x, hx⟩ := card_eq_one.1 (le_antisymm (by omega) (card_pos.2 (cne hAu)))
      exact hAc (hx ▸ σ.singleton_mem x)
    rw [← σ.unrootedLength_of_compl_notMem hA hAu hAc,
      ← σ'.unrootedLength_of_compl_notMem (hcl ▸ hA) hAu (hcl ▸ hAc)]
    exact hU.2 A (mem_unroot.2 (Or.inl ⟨hA, hAu⟩)) hA2 hAc2

theorem proposition11_theorem9_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' :=
  unrootedDist_eq_iff_four hX σ σ'

theorem proposition11_corollary10 (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X) =
      σ'.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X)) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} := by
  let L := Σ x, Fin (min (ℓ x) 2)
  let s' : L → X := Sigma.fst
  have h' : σ.unrootedDist s' = σ'.unrootedDist s' :=
    unrootedDist_comp_eq h (.sigmaMap (.refl X) fun _ => Fin.castLEEmb (min_le_left _ _))
  let f0 : X → L := fun x => ⟨x, 0, lt_min (hℓ x) (by decide)⟩
  let pre : Finset X → Finset L := fun A => A.sigma fun _ => univ
  have mem_pre : ∀ {A : Finset X} {p : L}, p ∈ pre A ↔ p.1 ∈ A :=
    fun {_ _} => mem_sigma.trans (and_iff_left (mem_univ _))
  have pre_sub : ∀ {A B : Finset X}, pre A ⊆ pre B ↔ A ⊆ B := fun {A B} =>
    ⟨fun h x hx => mem_pre.1 (h (mem_pre.2 hx : f0 x ∈ pre A)), fun h _ hp => mem_pre.2 (h (mem_pre.1 hp))⟩
  have pre_inj : ∀ {A B : Finset X}, pre A = pre B ↔ A = B :=
    ⟨fun h => Subset.antisymm (pre_sub.1 h.le) (pre_sub.1 h.ge), fun h => h ▸ rfl⟩
  have pre_ssub : ∀ {A B : Finset X}, pre A ⊂ pre B ↔ A ⊂ B := by
    simp [Finset.ssubset_iff_subset_ne, pre_sub, pre_inj]
  have pre_u : pre univ = univ := by ext; simp [mem_pre]
  have pre_ne : ∀ {A : Finset X}, A.Nonempty → (pre A).Nonempty := fun ⟨x, hx⟩ => ⟨f0 x, mem_pre.2 hx⟩
  have card_pre : ∀ A : Finset X, #(pre A) = ∑ x ∈ A, min (ℓ x) 2 := fun A => by
    show #(A.sigma fun _ => univ) = _; rw [card_sigma]; simp
  have le_pre : ∀ A : Finset X, #A ≤ #(pre A) := fun A => by
    rw [card_eq_sum_ones, card_pre]; exact sum_le_sum fun x _ => by have := hℓ x; omega
  let extT : SpeciesTree X → SpeciesTree L := fun ρ =>
    { clusters := ρ.clusters.image pre ∪ univ.image ({·})
      univ_mem := pre_u ▸ mem_union_left _ (mem_image_of_mem _ ρ.univ_mem)
      singleton_mem l := mem_union_right _ (mem_image_of_mem _ (mem_univ l))
      nonempty_of_mem B hB := by
        rcases mem_union.1 hB with hB | hB
        · obtain ⟨A, hA, rfl⟩ := mem_image.1 hB; exact pre_ne (ρ.nonempty_of_mem A hA)
        · obtain ⟨l, -, rfl⟩ := mem_image.1 hB; exact singleton_nonempty l
      laminar B hB C hC := by
        have slam : ∀ (l : L) (D : Finset L), {l} ⊆ D ∨ D ⊆ {l} ∨ Disjoint {l} D := fun l D =>
          if hl : l ∈ D then Or.inl (singleton_subset_iff.2 hl) else Or.inr (Or.inr (disjoint_singleton_left.2 hl))
        rcases mem_union.1 hB with hB | hB
        · obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
          rcases mem_union.1 hC with hC | hC
          · obtain ⟨A', hA', rfl⟩ := mem_image.1 hC
            rcases ρ.laminar A hA A' hA' with h | h | h
            · exact Or.inl (pre_sub.2 h)
            · exact Or.inr (Or.inl (pre_sub.2 h))
            · exact Or.inr (Or.inr (disjoint_left.2 fun _ h1 h2 => disjoint_left.1 h (mem_pre.1 h1) (mem_pre.1 h2)))
          · obtain ⟨l, -, rfl⟩ := mem_image.1 hC
            rcases slam l (pre A) with h | h | h; exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h.symm)]
        · obtain ⟨l, -, rfl⟩ := mem_image.1 hB; exact slam l C
      length B := if h : ∃ A ∈ ρ.clusters, pre A = B ∧ 2 ≤ #B then ρ.length h.choose else 1
      length_pos B _ hBu := by
        split_ifs with h
        · obtain ⟨hA, hAB, -⟩ := h.choose_spec
          exact ρ.length_pos _ hA fun hu => hBu (hAB ▸ hu ▸ pre_u)
        · exact one_pos }
  have ext_len : ∀ (ρ : SpeciesTree X) {A}, A ∈ ρ.clusters → 2 ≤ #(pre A) → (extT ρ).length (pre A) = ρ.length A :=
    fun ρ {A} hA h2 => by
      have h : ∃ A' ∈ ρ.clusters, pre A' = pre A ∧ 2 ≤ #(pre A) := ⟨A, hA, rfl, h2⟩
      show dite _ _ _ = _; rw [dite_eq_left h, pre_inj.1 h.choose_spec.2.1]
  have hext : (extT σ).unrootedDist id = (extT σ').unrootedDist id := by
    have rde : ∀ (ρ : SpeciesTree X) G, ρ.rootedDist s' G = (extT ρ).rootedDist id G := fun ρ G => by
      let τ := extT ρ
      have hE := τ.isHierarchy
      have hpk : ∀ {A}, A ∈ ρ.clusters → 2 ≤ #(pre A) →
          populationKernel (L := L) ρ.length A = populationKernel τ.length (pre A) := fun {A} hA hp2 => by
        by_cases hAu : A = univ
        · subst hAu; rw [populationKernel_univ, pre_u, populationKernel_univ]
        · rw [populationKernel_ne_univ _ hAu,
            populationKernel_ne_univ _ (fun e => hAu (pre_inj.1 (e.trans pre_u.symm))), ext_len ρ hA hp2]
      have hsf : ∀ A, sampledForest s' A = sampledForest id (pre A) := fun A => by
        unfold sampledForest; congr 1; ext; simp [mem_pre, s']
      have key : ∀ {A}, A ∈ ρ.clusters → ∀ G,
          forestDist ρ.clusters ρ.length s' A G = forestDist τ.clusters τ.length id (pre A) G := by
        intro A; induction A using Finset.strongInduction with
        | H A ih =>
        intro hA G
        obtain ⟨x, hx⟩ := ρ.nonempty_of_mem A hA
        rcases Nat.lt_or_ge 1 #A with hA2 | hA1
        · have hp2 : 2 ≤ #(pre A) := (show 2 ≤ #A from hA2).trans (le_pre A)
          have hch : childClusters τ.clusters (pre A) = (childClusters ρ.clusters A).image pre := by
            ext C; rw [mem_image]; constructor
            · intro hC
              obtain ⟨hCE, hCA, hmax⟩ := mem_childClusters.1 hC
              rcases mem_union.1 hCE with hCE | hCE
              · obtain ⟨D, hD, rfl⟩ := mem_image.1 hCE
                exact ⟨D, mem_childClusters.2 ⟨hD, pre_ssub.1 hCA, fun D' hD' h1 h2' =>
                  hmax _ (mem_union_left _ (mem_image_of_mem _ hD')) (pre_ssub.2 h1) (pre_ssub.2 h2')⟩, rfl⟩
              · obtain ⟨l, -, rfl⟩ := mem_image.1 hCE
                obtain ⟨B, hB, hlB⟩ := ρ.isHierarchy.exists_mem_childClusters hA2
                  (mem_pre.1 (hCA.subset (mem_singleton_self l)))
                have hsub : {l} ⊆ pre B := singleton_subset_iff.2 (mem_pre.2 hlB)
                exact ⟨B, hB, (hsub.eq_or_ssubset.resolve_right fun hlt =>
                  hmax _ (mem_union_left _ (mem_image_of_mem _ (mem_childClusters.1 hB).1)) hlt
                    (pre_ssub.2 (mem_childClusters.1 hB).2.1)).symm⟩
            · rintro ⟨B, hB, rfl⟩
              obtain ⟨hBH, hBA, hmax⟩ := mem_childClusters.1 hB
              refine mem_childClusters.2 ⟨mem_union_left _ (mem_image_of_mem _ hBH),
                pre_ssub.2 hBA, fun C hC hBC hCA => ?_⟩
              rcases mem_union.1 hC with hC | hC
              · obtain ⟨D, hD, rfl⟩ := mem_image.1 hC
                exact hmax D hD (pre_ssub.1 hBC) (pre_ssub.1 hCA)
              · obtain ⟨l, -, rfl⟩ := mem_image.1 hC
                exact (pre_ne (ρ.nonempty_of_mem B hBH)).ne_empty (ssubset_singleton_iff.1 hBC)
          let e : childClusters ρ.clusters A ≃ childClusters τ.clusters (pre A) :=
            Equiv.ofBijective (fun B => ⟨pre B.1, hch ▸ mem_image_of_mem _ B.2⟩)
              ⟨fun B B' h => Subtype.ext (pre_inj.1 (congrArg Subtype.val h)), fun C => by
                obtain ⟨B, hB, hBC⟩ := mem_image.1 (by rw [← hch]; exact C.2)
                exact ⟨⟨B, hB⟩, Subtype.ext hBC⟩⟩
          rw [forestDist_eq_sum_entering, forestDist_eq_sum_entering, hpk hA hp2]
          exact sum_congr rfl fun F _ => congrArg (· * _) <| by
            rw [enteringDist, enteringDist, hsf A]
            exact csum_equiv e (fun B => funext (ih B.1 (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1)) _
        · obtain rfl : A = {x} := eq_singleton_iff_unique_mem.2 ⟨hx, fun y hy => card_le_one.1 hA1 y hy x hx⟩
          have hps : univ.filter (fun l => s' l = x) = pre {x} := by ext; simp [mem_pre, s']
          have hcx : #(pre {x}) = min (ℓ x) 2 := by simp [card_pre]
          rcases (show #(pre {x}) = 1 ∨ #(pre {x}) = 2 by have := hℓ x; omega) with h1 | h2'
          · obtain ⟨l, hl⟩ := card_eq_one.1 h1
            rw [forestDist_singleton_of_card_le_one ρ.isHierarchy ρ.length (hps ▸ h1.le), hsf {x}, hl,
              forestDist_id_singleton hE]
            congr 2; ext; simp [sampledForest, eq_comm]
          · obtain ⟨l₁, l₂, hne, hl⟩ := card_eq_two.1 h2'
            have hch := hE.childClusters_eq_pair (τ.singleton_mem l₁) (τ.singleton_mem l₂)
              (disjoint_singleton.2 hne) (insert_eq l₁ {l₂}).symm
            rw [forestDist_of_childClusters_eq_empty (ρ.isHierarchy.childClusters_singleton x),
              hpk hA h2'.ge, hsf {x}]
            conv_rhs =>
              rw [hl, forestDist_of_childClusters_eq_pair hch (by simpa using hne)]
              simp only [forestDist_id_singleton hE, ite_mul, one_mul, zero_mul, sum_ite_irrel,
                sum_const_zero, sum_ite_eq', mem_univ, ite_true]
            refine congrArg₂ (fun D S => populationKernel τ.length D S G) hl ?_
            rw [hl]
            exact (union_eq_right.2 fun C hC => by
              rcases mem_union.1 hC with hC | hC <;> cases mem_singleton.1 hC <;>
                simp [singleton_mem_sampledForest]).symm
      unfold SpeciesTree.rootedDist
      rw [key ρ.univ_mem G, pre_u]
    have e1 : ∀ τ : SpeciesTree X, (extT τ).unrootedDist id = τ.unrootedDist s' :=
      fun τ => funext fun T => by unfold SpeciesTree.unrootedDist; simp_rw [← rde τ]
    rw [e1, e1, h']
  have h5 : 5 ≤ Fintype.card L := by
    have : Fintype.card L = #(pre univ) := by rw [pre_u, card_univ]
    rw [this, card_pre, show ∑ z ∈ univ, min (ℓ z) 2 = Fintype.card X + ∑ z, (min (ℓ z) 2 - 1) from by
      rw [show Fintype.card X = ∑ _ : X, 1 by simp, ← sum_add_distrib]
      exact sum_congr rfl fun z _ => by have := hℓ z; omega]
    rcases hcond with ⟨h4, x, hx⟩ | ⟨h3, x, y, hxy, hx, hy⟩
    · have := single_le_sum (f := fun z => min (ℓ z) 2 - 1) (fun _ _ => Nat.zero_le _) (mem_univ x); omega
    · have := sum_le_sum_of_subset (f := fun z => min (ℓ z) 2 - 1) (subset_univ {x, y})
      rw [sum_pair hxy] at this; omega
  obtain ⟨hcl, hlen⟩ := proposition11_theorem9 h5 _ _ hext
  have hmem : ∀ {τ τ' : SpeciesTree X}, (extT τ).clusters = (extT τ').clusters →
      ∀ A ∈ τ.clusters, A ∈ τ'.clusters := fun {τ τ'} hcl' A hA => by
    rcases mem_union.1 (hcl' ▸ mem_union_left _ (mem_image_of_mem _ hA) : pre A ∈ (extT τ').clusters) with h1 | h1
    · obtain ⟨A', hA', hA'A⟩ := mem_image.1 h1; exact pre_inj.1 hA'A ▸ hA'
    · obtain ⟨l, -, hl⟩ := mem_image.1 h1
      have hsub : A ⊆ {l.1} := fun y hy =>
        mem_singleton.2 (congrArg Sigma.fst (mem_singleton.1 (hl ▸ mem_pre.2 hy : f0 y ∈ {l})))
      exact Subset.antisymm hsub (singleton_subset_iff.2 (mem_pre.1 (hl.symm ▸ mem_singleton_self l))) ▸
        τ'.singleton_mem l.1
  have hcl' := Subset.antisymm (hmem hcl) (hmem hcl.symm)
  have key : ∀ A ∈ σ.clusters, 2 ≤ #(pre A) → A ≠ univ → σ.length A = σ'.length A := fun A hA hp2 hAu => by
    have := hlen _ (mem_union_left _ (mem_image_of_mem _ hA)) hp2 fun e => hAu (pre_inj.1 (e.trans pre_u.symm))
    rwa [ext_len σ hA hp2, ext_len σ' (hcl' ▸ hA) hp2] at this
  refine ⟨⟨hcl', fun A hA hA2 hAu => key A hA (hA2.trans (le_pre A)) hAu⟩,
    fun x hx => key {x} (σ.singleton_mem x) (by simp [card_pre, hx]) fun hxu => ?_⟩
  have := congrArg card hxu; simp at this; rcases hcond with ⟨_, -⟩ | ⟨_, -⟩ <;> omega

theorem theorem9 (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X) (_ : σ.IsBinary)
    (_ : σ'.IsBinary) (h : σ.unrootedDist id = σ'.unrootedDist id) :
    σ.SameRootedMetricTree σ' :=
  proposition11_theorem9 hX σ σ' h

theorem theorem9_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) (_ : σ.IsBinary)
    (_ : σ'.IsBinary) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' :=
  unrootedDist_eq_iff_four hX σ σ'

theorem corollary10 (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X) (_ : σ.IsBinary) (_ : σ'.IsBinary)
    (h : σ.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X) =
      σ'.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X)) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} :=
  proposition11_corollary10 ℓ hℓ hcond σ σ' h

theorem proposition3 (hX : Fintype.card X = 4) :
    (∀ σ σ' : SpeciesTree X, σ.IsBinary → σ'.IsBinary →
        σ.unrootedDist id = σ'.unrootedDist id → σ.SameUnrootedMetricTree σ') ∧
      ∃ σ σ' : SpeciesTree X, σ.IsBinary ∧ σ'.IsBinary ∧
        σ.unrootedDist id = σ'.unrootedDist id ∧ ¬ σ.SameRootedMetricTree σ' := by
  refine ⟨fun σ σ' _ _ => (unrootedDist_eq_iff_four hX σ σ').1, ?_⟩
  let τ : SpeciesTree (Fin 4) := ⟨caterpillar4, by decide, by decide, by decide, by decide,
    fun _ => 1, fun _ _ _ => one_pos⟩
  let τ' := τ.relabel (Equiv.swap 2 3)
  have hb : τ.IsBinary := by show ∀ A ∈ caterpillar4, _; decide
  have hu : τ.SameUnrootedMetricTree τ' := ⟨by show unroot caterpillar4 = _; decide, fun A _ _ _ => by
    simp only [SpeciesTree.unrootedLength, τ', SpeciesTree.relabel,
      show τ.clusters = caterpillar4 from rfl, show ∀ C, τ.length C = 1 from fun _ => rfl,
      sum_const, nsmul_one]
    exact congrArg Nat.cast (by revert A; decide)⟩
  let e : Fin 4 ≃ X := (Fintype.equivFinOfCardEq hX).symm
  exact ⟨τ.relabel e, τ'.relabel e, hb.relabel e, (hb.relabel _).relabel e,
    (SpeciesTree.unrootedDist_relabel_eq_iff τ τ' e).2
      ((unrootedDist_eq_iff_four (Fintype.card_fin 4) τ τ').2 hu),
    fun hs => (by decide : caterpillar4 ≠ relabelFamily (Equiv.swap 2 3) caterpillar4)
      ((SpeciesTree.sameRootedMetricTree_relabel_iff τ τ' e).1 hs).1⟩

end ADR11.Challenge
