module

public import ADR11.MSC.Basic

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] {Y : Type*} [Fintype Y] [DecidableEq Y]

def relabelFamily (e : X ≃ Y) (F : Finset (Finset X)) : Finset (Finset Y) :=
  F.image fun A => A.map e.toEmbedding

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
private lemma msc_map_symm_map (e : X ≃ Y) (A : Finset X) :
    (A.map e.toEmbedding).map e.symm.toEmbedding = A := by ext x; simp

private lemma msc_map_compl (e : X ≃ Y) (A : Finset X) :
    (A.map e.toEmbedding)ᶜ = Aᶜ.map e.toEmbedding := by ext y; simp [Finset.mem_map_equiv]

omit [DecidableEq X] [DecidableEq Y] in
private lemma msc_map_eq_univ_iff (e : X ≃ Y) (A : Finset X) :
    A.map e.toEmbedding = univ ↔ A = univ := by
  rw [← Finset.map_univ_equiv e, Finset.map_inj]

omit [Fintype X] [DecidableEq X] [Fintype Y] in
theorem relabelFamily_injective (e : X ≃ Y) : Function.Injective (relabelFamily e) :=
  Finset.image_injective (Finset.map_injective e.toEmbedding)

omit [Fintype X] [Fintype Y] in
theorem relabelFamily_symm (e : X ≃ Y) (F : Finset (Finset X)) :
    relabelFamily e.symm (relabelFamily e F) = F := by
  unfold relabelFamily; rw [image_image]
  conv_rhs => rw [← image_id (s := F)]
  congr 1; funext A; exact msc_map_symm_map e A

theorem unroot_relabelFamily (e : X ≃ Y) (F : Finset (Finset X)) :
    unroot (relabelFamily e F) = relabelFamily e (unroot F) := by
  have herase : (relabelFamily e F).erase univ = relabelFamily e (F.erase univ) := by
    unfold relabelFamily
    rw [Finset.image_erase (Finset.map_injective e.toEmbedding), Finset.map_univ_equiv]
  unfold unroot
  rw [herase]
  unfold relabelFamily
  rw [image_union, image_image, image_image]
  congr 2; funext A; exact msc_map_compl e A

def relabelFamilyEquiv (e : X ≃ Y) : Finset (Finset X) ≃ Finset (Finset Y) where
  toFun := relabelFamily e
  invFun := relabelFamily e.symm
  left_inv := relabelFamily_symm e
  right_inv := fun F => by simpa using relabelFamily_symm e.symm F

omit [Fintype X] [Fintype Y] in
@[simp] theorem relabelFamilyEquiv_apply (e : X ≃ Y) (F : Finset (Finset X)) :
    relabelFamilyEquiv e F = relabelFamily e F := rfl

omit [Fintype X] [DecidableEq X] [Fintype Y] in
theorem mem_relabelFamily {e : X ≃ Y} {F : Finset (Finset X)} {B : Finset Y} :
    B ∈ relabelFamily e F ↔ B.map e.symm.toEmbedding ∈ F := by
  unfold relabelFamily; rw [mem_image]
  refine ⟨?_, fun h => ⟨_, h, by ext y; simp [Finset.mem_map_equiv]⟩⟩
  rintro ⟨A, hA, rfl⟩; rwa [msc_map_symm_map]

omit [Fintype X] [DecidableEq X] [Fintype Y] in
theorem map_mem_relabelFamily {e : X ≃ Y} {F : Finset (Finset X)} {A : Finset X} :
    A.map e.toEmbedding ∈ relabelFamily e F ↔ A ∈ F := by
  rw [mem_relabelFamily, msc_map_symm_map]

private lemma msc_exp_submatrix {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (π : n ≃ m) (A : Matrix m m ℝ) :
    NormedSpace.exp (A.submatrix π π) = (NormedSpace.exp A).submatrix π π := by
  have hpow : ∀ k : ℕ, (A.submatrix π π) ^ k = (A ^ k).submatrix π π := fun k => by
    induction k with
    | zero => simp [Matrix.submatrix_one_equiv]
    | succ k ih => rw [pow_succ, ih, Matrix.submatrix_mul_equiv, pow_succ]
  ext i j
  exact (fact_hasSum_exp_apply (A.submatrix π π) i j).unique
    (by simpa [hpow] using fact_hasSum_exp_apply A (π i) (π j))

theorem kingmanTransition_relabelFamily (e : X ≃ Y) (t : ℝ) (F G : Finset (Finset X)) :
    kingmanTransition t (relabelFamily e F) (relabelFamily e G) = kingmanTransition t F G := by
  have hroots : ∀ F : Finset (Finset X), roots (relabelFamily e F) = relabelFamily e (roots F) :=
    fun F => by
      unfold roots relabelFamily; rw [filter_image]; congr 1
      refine filter_congr fun A _ => ?_
      rw [Finset.forall_mem_image]
      exact ⟨fun h B hB hAB => Finset.map_injective _ (h hB (Finset.map_subset_map.2 hAB)),
        fun h B hB hAB => by rw [h B hB (Finset.map_subset_map.1 hAB)]⟩
  have hQ : (kingmanGenerator (L := Y)).submatrix (relabelFamilyEquiv e) (relabelFamilyEquiv e) =
      kingmanGenerator (L := X) := by
    ext F G
    show kingmanGenerator (relabelFamily e F) (relabelFamily e G) = kingmanGenerator F G
    unfold kingmanGenerator
    rw [hroots, show #(relabelFamily e (roots F)) = #(roots F) from
      card_image_of_injective _ (Finset.map_injective e.toEmbedding)]
    by_cases hGF : G = F
    · subst hGF; simp
    · rw [ite_eq_right (fun h => hGF (relabelFamily_injective e h)), ite_eq_right hGF]
      refine if_congr ⟨?_, ?_⟩ rfl rfl
      · rintro ⟨A', hA', B', hB', hAB', hF⟩
        obtain ⟨A, hA, rfl⟩ := mem_image.1 hA'
        obtain ⟨B, hB, rfl⟩ := mem_image.1 hB'
        refine ⟨A, hA, B, hB, fun h => hAB' (h ▸ rfl), relabelFamily_injective e ?_⟩
        rw [hF]; unfold relabelFamily; rw [image_insert, Finset.map_union]
      · rintro ⟨A, hA, B, hB, hAB, rfl⟩
        refine ⟨A.map e.toEmbedding, mem_image_of_mem _ hA, B.map e.toEmbedding,
          mem_image_of_mem _ hB, fun h => hAB (Finset.map_injective _ h), ?_⟩
        unfold relabelFamily; rw [image_insert, Finset.map_union]
  have hs : t • (kingmanGenerator (L := Y)).submatrix (relabelFamilyEquiv e)
      (relabelFamilyEquiv e) = (t • kingmanGenerator (L := Y)).submatrix (relabelFamilyEquiv e)
      (relabelFamilyEquiv e) := rfl
  unfold kingmanTransition
  rw [← hQ, hs, msc_exp_submatrix]
  rfl

theorem forestDist_relabel (e : X ≃ Y) (H : Finset (Finset X)) (len : Finset X → ℝ)
    (A : Finset X) (G : Finset (Finset X)) :
    forestDist (relabelFamily e H) (fun B => len (B.map e.symm.toEmbedding)) id
      (A.map e.toEmbedding) (relabelFamily e G) = forestDist H len id A G := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist.eq_1 (relabelFamily e H), forestDist.eq_1 H]
  have hch : childClusters (relabelFamily e H) (A.map e.toEmbedding) =
      relabelFamily e (childClusters H A) := by
    unfold childClusters relabelFamily; rw [filter_image]; congr 1
    exact filter_congr fun B _ => by simp only [Finset.map_ssubset_map, Finset.forall_mem_image]
  let ψ : childClusters H A ≃ childClusters (relabelFamily e H) (A.map e.toEmbedding) :=
    (Equiv.finsetCongr e).subtypeEquiv fun B => by
      rw [hch, Equiv.finsetCongr_apply, map_mem_relabelFamily]
  let Φ := ψ.arrowCongr (relabelFamilyEquiv e)
  rw [← Φ.sum_comp]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hΦ : ∀ B : childClusters H A, Φ f (ψ B) = relabelFamily e (f B) := fun B => by
    simp [Φ, Equiv.arrowCongr_apply]
  congr 1
  · rw [← ψ.prod_comp]
    refine Finset.prod_congr rfl fun B _ => ?_
    rw [hΦ]
    exact ih B (mem_childClusters.1 B.2).2.1 (f B)
  · have hsup : univ.sup (Φ f) ∪ sampledForest id (A.map e.toEmbedding) =
        relabelFamily e (univ.sup f ∪ sampledForest id A) := by
      have h1 : univ.sup (Φ f) = relabelFamily e (univ.sup f) := by
        rw [Finset.apply_sup_eq_sup_comp (relabelFamily e) (fun F G => image_union F G) (image_empty _),
          ← Finset.map_univ_equiv ψ, Finset.sup_map]
        exact Finset.sup_congr rfl fun B _ => hΦ B
      have h2 : sampledForest id (A.map e.toEmbedding) = relabelFamily e (sampledForest id A) := by
        ext C; unfold relabelFamily; simp only [mem_sampledForest, mem_image]
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨{e.symm y}, ⟨e.symm y, by simpa [Finset.mem_map_equiv] using hy, rfl⟩, by simp⟩
        · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
          exact ⟨e x, Finset.mem_map_of_mem _ hx, by simp⟩
      rw [h1, h2]; exact (image_union _ _).symm
    unfold populationKernel
    by_cases hA : A = univ
    · rw [ite_eq_left ((msc_map_eq_univ_iff e A).2 hA), ite_eq_left hA, hsup]
      unfold kingmanAbsorption
      simp_rw [kingmanTransition_relabelFamily]
    · rw [ite_eq_right (mt (msc_map_eq_univ_iff e A).1 hA), ite_eq_right hA, hsup]
      dsimp only
      rw [msc_map_symm_map, kingmanTransition_relabelFamily]

def SpeciesTree.relabel (σ : SpeciesTree X) (e : X ≃ Y) : SpeciesTree Y where
  clusters := relabelFamily e σ.clusters
  univ_mem := mem_image.2 ⟨univ, σ.univ_mem, Finset.map_univ_equiv e⟩
  singleton_mem y := mem_image.2 ⟨{e.symm y}, σ.singleton_mem _, by simp⟩
  nonempty_of_mem B hB := by
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
    exact Finset.map_nonempty.2 (σ.nonempty_of_mem A hA)
  laminar B hB C hC := by
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
    obtain ⟨A', hA', rfl⟩ := mem_image.1 hC
    rw [Finset.map_subset_map, Finset.map_subset_map, Finset.disjoint_map]
    exact σ.laminar A hA A' hA'
  length B := σ.length (B.map e.symm.toEmbedding)
  length_pos B hB hBu := by
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
    rw [msc_map_symm_map]
    exact σ.length_pos A hA fun h => hBu ((msc_map_eq_univ_iff e A).2 h)

@[simp] theorem SpeciesTree.relabel_clusters (σ : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).clusters = relabelFamily e σ.clusters := rfl

theorem SpeciesTree.relabel_length (σ : SpeciesTree X) (e : X ≃ Y) (B : Finset Y) :
    (σ.relabel e).length B = σ.length (B.map e.symm.toEmbedding) := rfl

@[simp] theorem SpeciesTree.relabel_length_map (σ : SpeciesTree X) (e : X ≃ Y) (A : Finset X) :
    (σ.relabel e).length (A.map e.toEmbedding) = σ.length A := by
  rw [SpeciesTree.relabel_length, msc_map_symm_map]

theorem SpeciesTree.relabel_relabel_symm (σ : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).relabel e.symm = σ := by
  have h1 := relabelFamily_symm e σ.clusters
  have h2 : (fun A : Finset X => σ.length ((A.map e.symm.symm.toEmbedding).map e.symm.toEmbedding)) =
      σ.length := funext fun A => by rw [Equiv.symm_symm, msc_map_symm_map]
  cases σ; dsimp only [SpeciesTree.relabel] at h1 h2 ⊢; congr

theorem SpeciesTree.isBinary_relabel {σ : SpeciesTree X} (e : X ≃ Y) (h : σ.IsBinary) :
    (σ.relabel e).IsBinary := by
  intro B hB hB2
  obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
  rw [Finset.card_map] at hB2
  obtain ⟨C, hC, D, hD, hCD, hCDA⟩ := h A hA hB2
  refine ⟨C.map e.toEmbedding, mem_image_of_mem _ hC, D.map e.toEmbedding, mem_image_of_mem _ hD,
    (Finset.disjoint_map _).2 hCD, ?_⟩
  rw [← Finset.map_union, hCDA]

theorem SpeciesTree.unrootedDist_relabel (σ : SpeciesTree X) (e : X ≃ Y)
    (T : Finset (Finset X)) :
    (σ.relabel e).unrootedDist id (relabelFamily e T) = σ.unrootedDist id T := by
  unfold SpeciesTree.unrootedDist SpeciesTree.rootedDist
  rw [← (relabelFamilyEquiv e).sum_comp]
  refine Finset.sum_congr rfl fun G _ => ?_
  have hr := forestDist_relabel e σ.clusters σ.length univ G
  rw [Finset.map_univ_equiv] at hr
  simp only [relabelFamilyEquiv_apply, unroot_relabelFamily, (relabelFamily_injective e).eq_iff]
  exact if_congr Iff.rfl hr rfl

private lemma msc_unrootedDist_of_relabel (σ σ' : SpeciesTree X) (e : X ≃ Y)
    (h : (σ.relabel e).unrootedDist id = (σ'.relabel e).unrootedDist id) :
    σ.unrootedDist id = σ'.unrootedDist id :=
  funext fun T => by simpa [SpeciesTree.unrootedDist_relabel] using congrFun h (relabelFamily e T)

theorem SpeciesTree.unrootedDist_relabel_eq_iff (σ σ' : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).unrootedDist id = (σ'.relabel e).unrootedDist id ↔
      σ.unrootedDist id = σ'.unrootedDist id :=
  ⟨msc_unrootedDist_of_relabel σ σ' e, fun h => msc_unrootedDist_of_relabel _ _ e.symm
    (by rwa [σ.relabel_relabel_symm e, σ'.relabel_relabel_symm e])⟩

private lemma msc_sameRooted_of_relabel (σ σ' : SpeciesTree X) (e : X ≃ Y)
    (h : (σ.relabel e).SameRootedMetricTree (σ'.relabel e)) : σ.SameRootedMetricTree σ' := by
  refine ⟨relabelFamily_injective e h.1, fun A hA hA2 hAu => ?_⟩
  have := h.2 (A.map e.toEmbedding) (map_mem_relabelFamily.2 hA) (by rwa [Finset.card_map])
    fun h' => hAu ((msc_map_eq_univ_iff e A).1 h')
  rwa [SpeciesTree.relabel_length_map, SpeciesTree.relabel_length_map] at this

theorem SpeciesTree.sameRootedMetricTree_relabel_iff (σ σ' : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).SameRootedMetricTree (σ'.relabel e) ↔ σ.SameRootedMetricTree σ' :=
  ⟨msc_sameRooted_of_relabel σ σ' e, fun h => msc_sameRooted_of_relabel _ _ e.symm
    (by simpa [relabel_relabel_symm] using h)⟩

theorem SpeciesTree.unrootedLength_relabel (σ : SpeciesTree X) (e : X ≃ Y) (A : Finset X) :
    (σ.relabel e).unrootedLength (A.map e.toEmbedding) = σ.unrootedLength A := by
  unfold SpeciesTree.unrootedLength
  rw [SpeciesTree.relabel_clusters]
  unfold relabelFamily
  rw [filter_image, sum_image fun x _ y _ h => Finset.map_injective _ h]
  refine Finset.sum_congr (filter_congr fun C _ => ?_) fun C _ =>
    SpeciesTree.relabel_length_map σ e C
  simp only [ne_eq, msc_map_eq_univ_iff, Finset.map_inj, msc_map_compl]

private lemma msc_sameUnrooted_of_relabel (σ σ' : SpeciesTree X) (e : X ≃ Y)
    (h : (σ.relabel e).SameUnrootedMetricTree (σ'.relabel e)) : σ.SameUnrootedMetricTree σ' := by
  have h1 := h.1
  simp only [SpeciesTree.relabel_clusters, unroot_relabelFamily] at h1
  refine ⟨relabelFamily_injective e h1, fun A hA hA2 hAc2 => ?_⟩
  have := h.2 (A.map e.toEmbedding)
    (by rw [SpeciesTree.relabel_clusters, unroot_relabelFamily, map_mem_relabelFamily]; exact hA)
    (by rwa [Finset.card_map]) (by rwa [msc_map_compl, Finset.card_map])
  rwa [SpeciesTree.unrootedLength_relabel, SpeciesTree.unrootedLength_relabel] at this

theorem SpeciesTree.sameUnrootedMetricTree_relabel_iff (σ σ' : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).SameUnrootedMetricTree (σ'.relabel e) ↔ σ.SameUnrootedMetricTree σ' :=
  ⟨msc_sameUnrooted_of_relabel σ σ' e, fun h => msc_sameUnrooted_of_relabel _ _ e.symm
    (by simpa [relabel_relabel_symm] using h)⟩

/-! ### Classification on 4 and 5 taxa -/

def U4 : ℕ → Finset (Finset (Fin 4))
  | 1 => treeOfClusters {{0, 1}}
  | _ => treeOfClusters ∅

def U5 : ℕ → Finset (Finset (Fin 5))
  | 2 => treeOfClusters {{0, 1}, {3, 4}}
  | 1 => treeOfClusters {{0, 1}}
  | _ => treeOfClusters ∅

def rootings4 : ℕ → Finset (Finset (Finset (Fin 4)))
  | 1 => {hierarchyOf {{0, 1}, {0, 1, 2}}, hierarchyOf {{0, 1}, {0, 1, 3}},
          hierarchyOf {{2, 3}, {0, 2, 3}}, hierarchyOf {{2, 3}, {1, 2, 3}},
          hierarchyOf {{0, 1}, {2, 3}}, hierarchyOf {{0, 1}}, hierarchyOf {{2, 3}}}
  | _ => {hierarchyOf ∅, hierarchyOf {{0, 1, 2}}, hierarchyOf {{0, 1, 3}},
          hierarchyOf {{0, 2, 3}}, hierarchyOf {{1, 2, 3}}}

def rootings5 : ℕ → Finset (Finset (Finset (Fin 5)))
  | 2 => {hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 3}}, hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 4}},
          hierarchyOf {{3, 4}, {2, 3, 4}, {1, 2, 3, 4}}, hierarchyOf {{3, 4}, {2, 3, 4}, {0, 2, 3, 4}},
          hierarchyOf {{0, 1}, {3, 4}, {0, 1, 3, 4}}, hierarchyOf {{0, 1}, {3, 4}, {0, 1, 2}},
          hierarchyOf {{3, 4}, {0, 1}, {2, 3, 4}},
          hierarchyOf {{0, 1}, {3, 4}}, hierarchyOf {{0, 1}, {0, 1, 2}},
          hierarchyOf {{3, 4}, {2, 3, 4}}}
  | 1 => {hierarchyOf {{0, 1}}, hierarchyOf {{2, 3, 4}}, hierarchyOf {{0, 1}, {2, 3, 4}},
          hierarchyOf {{2, 3, 4}, {1, 2, 3, 4}}, hierarchyOf {{2, 3, 4}, {0, 2, 3, 4}},
          hierarchyOf {{0, 1}, {0, 1, 3, 4}}, hierarchyOf {{0, 1}, {0, 1, 2, 4}},
          hierarchyOf {{0, 1}, {0, 1, 2, 3}}}
  | _ => {hierarchyOf ∅, hierarchyOf {{1, 2, 3, 4}}, hierarchyOf {{0, 2, 3, 4}},
          hierarchyOf {{0, 1, 3, 4}}, hierarchyOf {{0, 1, 2, 4}}, hierarchyOf {{0, 1, 2, 3}}}

def uOf (n : ℕ) (P : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  univ.filter fun A => #A = 1 ∨ #A = n - 1 ∨ A ∈ P ∨ Aᶜ ∈ P

private theorem classify_uOf_eq {n : ℕ} (hn : n = 4 ∨ n = 5) (τ : SpeciesTree (Fin n)) :
    unroot τ.clusters = uOf n ((unroot τ.clusters).filter fun B => #B = 2) := by
  have hsing : ∀ x : Fin n, {x} ∈ unroot τ.clusters := fun x =>
    mem_unroot.2 (Or.inl ⟨τ.singleton_mem x, fun h => by
      have := congrArg card h; rw [card_singleton, card_univ, Fintype.card_fin] at this; omega⟩)
  ext A
  simp only [uOf, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    have hc : #Aᶜ = n - #A := by rw [card_compl, Fintype.card_fin]
    have h1 : 1 ≤ #A ∧ #A < n := by
      rcases mem_unroot.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨(τ.nonempty_of_mem A h1).card_pos, by
          simpa [Fintype.card_fin] using (card_lt_iff_ne_univ A).2 h2⟩
      · have h3 := (τ.nonempty_of_mem _ h1).card_pos
        have h4 : #Aᶜ < n := by simpa [Fintype.card_fin] using (card_lt_iff_ne_univ Aᶜ).2 h2
        omega
    rcases (by omega : #A = 1 ∨ #A = n - 1 ∨ #A = 2 ∨ #Aᶜ = 2) with h3 | h3 | h3 | h3
    · exact Or.inl h3
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (Or.inl ⟨h, h3⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨compl_mem_unroot.2 h, h3⟩))
  · rintro (h | h | ⟨h, -⟩ | ⟨h, -⟩)
    · obtain ⟨x, rfl⟩ := card_eq_one.1 h; exact hsing x
    · obtain ⟨x, hx⟩ := card_eq_one.1 (show #Aᶜ = 1 by rw [card_compl, Fintype.card_fin]; omega)
      exact compl_mem_unroot.1 (hx ▸ hsing x)
    · exact h
    · exact compl_mem_unroot.1 h

private abbrev lam (A B : Finset X) : Prop := A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype
set_option synthInstance.maxSize 2000

private theorem classify_exists_equiv_unroot {n : ℕ} (K : Finset ℕ)
    (U : ℕ → Finset (Finset (Fin n))) (hn : n = 4 ∨ n = 5) (hX : Fintype.card X = n)
    (σ : SpeciesTree X)
    (hdec : ∀ P ∈ ((univ : Finset (Finset (Fin n))).filter fun B => #B = 2).powerset,
      (∀ A ∈ P, ∀ B ∈ P, lam A B ∨ lam A Bᶜ ∨ lam Aᶜ B ∨ lam Aᶜ Bᶜ) →
      ∃ e ∈ (univ : Finset (Fin n ≃ Fin n)), ∃ k ∈ K,
        relabelFamily e (uOf n P) = U k := by decide +kernel) :
    ∃ e : Fin n ≃ X, ∃ k ∈ K, unroot (σ.relabel e.symm).clusters = U k := by
  let e₀ : X ≃ Fin n := Fintype.equivFinOfCardEq hX
  let τ := σ.relabel e₀
  obtain ⟨e, -, k, hk, he⟩ := hdec ((unroot τ.clusters).filter fun B => #B = 2)
    (mem_powerset.2 fun A hA => mem_filter.2 ⟨mem_univ A, (mem_filter.1 hA).2⟩)
    (fun A hA B hB => by
      rcases mem_unroot.1 (mem_filter.1 hA).1 with ⟨hA, -⟩ | ⟨hA, -⟩ <;>
        rcases mem_unroot.1 (mem_filter.1 hB).1 with ⟨hB, -⟩ | ⟨hB, -⟩
      · exact Or.inl (τ.laminar _ hA _ hB)
      · exact Or.inr (Or.inl (τ.laminar _ hA _ hB))
      · exact Or.inr (Or.inr (Or.inl (τ.laminar _ hA _ hB)))
      · exact Or.inr (Or.inr (Or.inr (τ.laminar _ hA _ hB))))
  refine ⟨(e₀.trans e).symm, k, hk, ?_⟩
  have hcomp : relabelFamily (e₀.trans e) σ.clusters = relabelFamily e τ.clusters := by
    unfold τ; rw [SpeciesTree.relabel_clusters]
    unfold relabelFamily; rw [image_image]; congr 1; funext A
    exact (Finset.map_map e₀.toEmbedding e.toEmbedding A).symm
  rw [SpeciesTree.relabel_clusters, Equiv.symm_symm, hcomp, unroot_relabelFamily,
    classify_uOf_eq hn τ, he]

theorem exists_equiv_unroot_eq_U4 (hX : Fintype.card X = 4) (σ : SpeciesTree X) :
    ∃ e : Fin 4 ≃ X, ∃ k ∈ ({0, 1} : Finset ℕ), unroot (σ.relabel e.symm).clusters = U4 k :=
  classify_exists_equiv_unroot {0, 1} U4 (Or.inl rfl) hX σ

theorem exists_equiv_unroot_eq_U5 (hX : Fintype.card X = 5) (σ : SpeciesTree X) :
    ∃ e : Fin 5 ≃ X, ∃ k ∈ ({0, 1, 2} : Finset ℕ),
      unroot (σ.relabel e.symm).clusters = U5 k :=
  classify_exists_equiv_unroot {0, 1, 2} U5 (Or.inr rfl) hX σ

theorem classify_eq_hierarchyOf {H : Finset (Finset X)} (hH : IsHierarchy H) :
    H = hierarchyOf (H.filter fun A => 2 ≤ #A ∧ A ≠ univ) := by
  ext A
  simp only [hierarchyOf, mem_insert, mem_union, mem_image, mem_univ, true_and, mem_filter]
  constructor
  · intro hA
    by_cases hu : A = univ
    · exact Or.inl hu
    · by_cases h2 : 2 ≤ #A
      · exact Or.inr (Or.inl ⟨hA, h2, hu⟩)
      · have : #A = 1 := by have := (hH.2.2.1 A hA).card_pos; omega
        obtain ⟨x, rfl⟩ := card_eq_one.1 this
        exact Or.inr (Or.inr ⟨x, rfl⟩)
  · rintro (rfl | ⟨hA, -⟩ | ⟨x, rfl⟩)
    · exact hH.1
    · exact hA
    · exact hH.2.1 x

private theorem classify_mem_of_unroot {n : ℕ} {τ : SpeciesTree (Fin n)} {U : Finset (Finset (Fin n))}
    {R : Finset (Finset (Finset (Fin n)))} (h : unroot τ.clusters = U)
    (hdec : ∀ N ∈ (U.filter fun A => 2 ≤ #A).powerset,
      (∀ A ∈ N, ∀ B ∈ N, lam A B) →
      unroot (hierarchyOf N) = U → hierarchyOf N ∈ R := by decide +kernel) :
    τ.clusters ∈ R := by
  have hH := classify_eq_hierarchyOf τ.isHierarchy
  rw [hH]
  refine hdec _ (mem_powerset.2 fun A hA => ?_)
    (fun A hA B hB => τ.laminar A (mem_filter.1 hA).1 B (mem_filter.1 hB).1)
    (by rw [← hH, h])
  obtain ⟨h1, h2, h3⟩ := mem_filter.1 hA
  exact mem_filter.2 ⟨h ▸ mem_unroot.2 (Or.inl ⟨h1, h3⟩), h2⟩

theorem classify_mem_rootings5 (τ : SpeciesTree (Fin 5)) (k : ℕ)
    (hk : k ∈ ({0, 1, 2} : Finset ℕ)) (h : unroot τ.clusters = U5 k) :
    τ.clusters ∈ rootings5 k := by
  simp only [mem_insert, mem_singleton] at hk
  rcases hk with rfl | rfl | rfl <;> exact classify_mem_of_unroot h

theorem mem_rootings4 (τ : SpeciesTree (Fin 4)) (k : ℕ) (hk : k ∈ ({0, 1} : Finset ℕ))
    (h : unroot τ.clusters = U4 k) : τ.clusters ∈ rootings4 k := by
  simp only [mem_insert, mem_singleton] at hk
  rcases hk with rfl | rfl <;> exact classify_mem_of_unroot h

end ADR11
