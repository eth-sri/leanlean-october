module

public import ADR11.MSC.Basic

@[expose] public section

namespace ADR11

open Finset

def relabelFamily {X Y : Type*} (e : X ≃ Y) : Finset (Finset X) → Finset (Finset Y) :=
  e.finsetCongr.finsetCongr

@[simp] theorem relabelFamily_refl {X : Type*} (F : Finset (Finset X)) :
    relabelFamily (.refl X) F = F := by simp [relabelFamily]

@[simp] lemma map_symm_map {X Y : Type*} (e : X ≃ Y) (A : Finset X) :
    (A.map e.toEmbedding).map e.symm.toEmbedding = A := by ext; simp

theorem relabelFamily_injective {X Y : Type*} (e : X ≃ Y) : Function.Injective (relabelFamily e) :=
  e.finsetCongr.finsetCongr.injective

section Relabel

lemma map_eq_univ_iff {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y) (A : Finset X) :
    A.map e.toEmbedding = univ ↔ A = univ := by rw [← map_univ_equiv e, map_inj]

variable {X : Type*} [Fintype X] [DecidableEq X] {Y : Type*} [Fintype Y] [DecidableEq Y]

lemma map_compl_eq (e : X ≃ Y) (A : Finset X) :
    (A.map e.toEmbedding)ᶜ = Aᶜ.map e.toEmbedding := by ext; simp [mem_map_equiv]

theorem unroot_relabelFamily (e : X ≃ Y) (F : Finset (Finset X)) :
    unroot (relabelFamily e F) = relabelFamily e (unroot F) := by
  ext B; simp [relabelFamily, mem_unroot, mem_map_equiv, Equiv.finsetCongr_symm, map_compl_eq, map_eq_univ_iff]

def SpeciesTree.relabel (σ : SpeciesTree X) (e : X ≃ Y) : SpeciesTree Y where
  clusters := relabelFamily e σ.clusters
  univ_mem := by simp [relabelFamily, mem_map_equiv, Equiv.finsetCongr_symm, map_univ_equiv, σ.univ_mem]
  singleton_mem y := by simp [relabelFamily, mem_map_equiv, Equiv.finsetCongr_symm, σ.singleton_mem]
  nonempty_of_mem B hB := by
    obtain ⟨A, hA, rfl⟩ := mem_map.1 hB; simpa using σ.nonempty_of_mem A hA
  laminar B hB C hC := by
    obtain ⟨A, hA, rfl⟩ := mem_map.1 hB; obtain ⟨A', hA', rfl⟩ := mem_map.1 hC
    simpa [disjoint_map] using σ.laminar A hA A' hA'
  length B := σ.length (e.symm.finsetCongr B)
  length_pos B hB hBu := by
    obtain ⟨A, hA, rfl⟩ := mem_map.1 hB
    simp only [Function.Embedding.coeFn_mk, ← Equiv.finsetCongr_symm, Equiv.symm_apply_apply]
    exact σ.length_pos A hA fun h => hBu (by simp [h, map_univ_equiv])

@[simp] theorem SpeciesTree.relabel_clusters (σ : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).clusters = relabelFamily e σ.clusters := rfl

@[simp] theorem SpeciesTree.relabel_length_map (σ : SpeciesTree X) (e : X ≃ Y) (A : Finset X) :
    (σ.relabel e).length (A.map e.toEmbedding) = σ.length A := by simp [SpeciesTree.relabel]

theorem SpeciesTree.IsBinary.relabel {σ : SpeciesTree X} (h : σ.IsBinary) (e : X ≃ Y) :
    (σ.relabel e).IsBinary := fun B hB hB2 => by
  obtain ⟨A, hA, rfl⟩ := mem_map.1 hB
  obtain ⟨C, hC, D, hD, hCD, hCDA⟩ := h A hA (by simpa using hB2)
  exact ⟨_, mem_map_of_mem _ hC, _, mem_map_of_mem _ hD,
    by simpa [disjoint_map] using hCD, by simp [← hCDA, map_union]⟩

theorem SpeciesTree.unrootedDist_relabel (σ : SpeciesTree X) (e : X ≃ Y) (T : Finset (Finset X)) :
    (σ.relabel e).unrootedDist id (relabelFamily e T) = σ.unrootedDist id T := by
  let eqv := e.finsetCongr.finsetCongr
  have heqv : ∀ F, eqv F = relabelFamily e F := fun _ => rfl
  have ktr : ∀ t F G, kingmanTransition t (relabelFamily e F) (relabelFamily e G) = kingmanTransition t F G := by
    have hgen : ∀ F G, kingmanGenerator (relabelFamily e F) (relabelFamily e G) =
        kingmanGenerator F G := fun F G => by
      have hr : roots (relabelFamily e F) = relabelFamily e (roots F) := by
        ext D; simp only [mem_roots, relabelFamily, Equiv.finsetCongr_apply, mem_map_equiv, Equiv.finsetCongr_symm]
        exact and_congr_right fun _ => ⟨fun h B hB hDB => by
            simpa using congrArg (map e.symm.toEmbedding)
              (h (B.map e.toEmbedding) (by simpa) (by simpa [← map_subset_map (f := e.symm.toEmbedding)])),
          fun h B hB hDB => by
            simpa [map_symm_map e.symm] using congrArg (map e.toEmbedding) (h _ hB (map_subset_map.2 hDB))⟩
      unfold kingmanGenerator
      rw [hr, show #(relabelFamily e (roots F)) = #(roots F) from card_map _]
      by_cases hGF : G = F
      · subst hGF; simp
      · rw [ite_eq_right (mt (relabelFamily_injective e ·) hGF), ite_eq_right hGF]
        refine if_congr ⟨?_, ?_⟩ rfl rfl
        · rintro ⟨A', hA', B', hB', hAB', hF⟩
          obtain ⟨A, hA, rfl⟩ := mem_map.1 hA'; obtain ⟨B, hB, rfl⟩ := mem_map.1 hB'
          refine ⟨A, hA, B, hB, fun h => hAB' (h ▸ rfl), relabelFamily_injective e ?_⟩
          rw [hF]; simp [relabelFamily, Equiv.finsetCongr_apply, map_insert, map_union]
        · rintro ⟨A, hA, B, hB, hAB, rfl⟩
          refine ⟨_, mem_map_of_mem _ hA, _, mem_map_of_mem _ hB, fun h => hAB (e.finsetCongr.injective h), ?_⟩
          simp [relabelFamily, Equiv.finsetCongr_apply, map_insert, map_union]
    intro t F G
    have hpow : ∀ n F G, ((t • kingmanGenerator (L := Y)) ^ n) (relabelFamily e F) (relabelFamily e G) =
        ((t • kingmanGenerator (L := X)) ^ n) F G := fun n => by
      induction n with
      | zero => intro F G; simp [pow_zero, one_apply_ite, (relabelFamily_injective e).eq_iff]
      | succ n ih =>
        intro F G
        rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply, ← eqv.sum_comp]
        exact sum_congr rfl fun H _ => by simp [heqv, hgen, ih H G]
    exact (hasSum_exp_apply _ _ _).unique ((hasSum_exp_apply _ _ _).congr_fun fun n => by rw [hpow])
  have key : ∀ (A : Finset X) (G : Finset (Finset X)),
      forestDist (relabelFamily e σ.clusters) (σ.relabel e).length id
        (A.map e.toEmbedding) (relabelFamily e G) =
      forestDist σ.clusters σ.length id A G := fun A => by
    induction A using Finset.strongInduction with
    | H A ih =>
    intro G
    rw [forestDist.eq_1 (relabelFamily e _), forestDist.eq_1 σ.clusters]
    have hch : childClusters (relabelFamily e σ.clusters) (A.map e.toEmbedding) =
        relabelFamily e (childClusters σ.clusters A) := by
      ext D; simp only [mem_childClusters, relabelFamily, Equiv.finsetCongr_apply, mem_map_equiv, Equiv.finsetCongr_symm]
      refine and_congr_right fun _ => ⟨fun ⟨hDA, hmax⟩ => ⟨by simpa [← map_ssubset_map (f := e.symm.toEmbedding)] using hDA,
          fun C hC hDC hCA => hmax (C.map e.toEmbedding) (by simpa)
            (by simpa [← map_ssubset_map (f := e.symm.toEmbedding)]) (map_ssubset_map.2 hCA)⟩,
        fun ⟨hDA, hmax⟩ => ⟨by simpa [← map_ssubset_map (f := e.symm.toEmbedding)] using hDA,
          fun C hC hDC hCA => hmax _ hC (map_ssubset_map.2 hDC)
            (by simpa [← map_ssubset_map (f := e.symm.toEmbedding)] using hCA)⟩⟩
    let ψ : childClusters σ.clusters A ≃
        childClusters (relabelFamily e σ.clusters) (A.map e.toEmbedding) :=
      (Equiv.finsetCongr e).subtypeEquiv fun B => by
        rw [hch]; simp [relabelFamily, mem_map_equiv, Equiv.finsetCongr_symm]
    let Φ := ψ.arrowCongr eqv
    rw [← Φ.sum_comp]
    refine sum_congr rfl fun f _ => ?_
    have hΦ : ∀ B, Φ f (ψ B) = relabelFamily e (f B) := fun _ => by simp [Φ, Equiv.arrowCongr_apply, heqv]
    congr 1
    · rw [← ψ.prod_comp]
      exact prod_congr rfl fun B _ => by rw [hΦ]; exact ih B (mem_childClusters.1 B.2).2.1 (f B)
    · have hsup : univ.sup (Φ f) = relabelFamily e (univ.sup f) := by
        rw [apply_sup_eq_sup_comp (relabelFamily e) (fun _ _ => map_union _ _) (map_empty _)]
        conv_lhs => rw [← map_univ_equiv ψ, sup_map]
        exact sup_congr rfl fun B _ => hΦ B
      have hsf : sampledForest id (A.map e.toEmbedding) = relabelFamily e (sampledForest id A) := by
        ext C; simp only [relabelFamily, Equiv.finsetCongr_apply, mem_sampledForest, mem_map_equiv,
          Equiv.finsetCongr_symm, id]
        exact ⟨fun ⟨y, hy, hC⟩ => ⟨e.symm y, hy, by simp [← hC]⟩,
          fun ⟨x, hx, hC⟩ => ⟨e x, by simpa using hx, by simpa [← hC] using map_symm_map e.symm C⟩⟩
      rw [show univ.sup (Φ f) ∪ sampledForest id (A.map e.toEmbedding) =
        relabelFamily e (univ.sup f ∪ sampledForest id A) by rw [hsup, hsf]; exact (map_union _ _).symm]
      by_cases hAu : A = univ
      · subst hAu; rw [map_univ_equiv, populationKernel_univ, populationKernel_univ]
        unfold kingmanAbsorption; simp_rw [ktr]
      · rw [populationKernel_ne_univ _ (mt (map_eq_univ_iff e A).1 hAu),
          populationKernel_ne_univ _ hAu, SpeciesTree.relabel_length_map, ktr]
  have hrd : ∀ G, (σ.relabel e).rootedDist id (relabelFamily e G) = σ.rootedDist id G := fun G => by
    unfold SpeciesTree.rootedDist; rw [SpeciesTree.relabel_clusters, ← map_univ_equiv e]; exact key univ G
  unfold SpeciesTree.unrootedDist
  rw [← eqv.sum_comp]
  exact sum_congr rfl fun G _ => by
    simp [heqv, unroot_relabelFamily, (relabelFamily_injective e).eq_iff, hrd]

theorem SpeciesTree.unrootedDist_relabel_eq_iff (σ σ' : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).unrootedDist id = (σ'.relabel e).unrootedDist id ↔
      σ.unrootedDist id = σ'.unrootedDist id :=
  ⟨fun h => funext fun T => by simpa [SpeciesTree.unrootedDist_relabel] using congrFun h (relabelFamily e T),
    fun h => funext fun T => by
      obtain ⟨T₀, rfl⟩ := e.finsetCongr.finsetCongr.surjective T
      exact (σ.unrootedDist_relabel e T₀).trans ((congrFun h T₀).trans (σ'.unrootedDist_relabel e T₀).symm)⟩

theorem SpeciesTree.sameRootedMetricTree_relabel_iff (σ σ' : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).SameRootedMetricTree (σ'.relabel e) ↔ σ.SameRootedMetricTree σ' := by
  refine and_congr (relabelFamily_injective e).eq_iff ⟨fun h A hA hA2 hAu => ?_, fun h B hB hB2 hBu => ?_⟩
  · simpa using h (A.map e.toEmbedding) (by simpa [relabelFamily, mem_map_equiv, Equiv.finsetCongr_symm] using hA)
      (by rwa [card_map]) (mt (map_eq_univ_iff e A).1 hAu)
  · obtain ⟨A, hA, rfl⟩ := mem_map.1 hB
    simp only [Function.Embedding.coeFn_mk, Equiv.finsetCongr_apply, SpeciesTree.relabel_length_map]
    exact h A hA (by simpa using hB2) (mt (map_eq_univ_iff e A).2 (by simpa using hBu))

theorem SpeciesTree.unrootedLength_relabel (σ : SpeciesTree X) (e : X ≃ Y) (A : Finset X) :
    (σ.relabel e).unrootedLength (A.map e.toEmbedding) = σ.unrootedLength A := by
  unfold SpeciesTree.unrootedLength; rw [SpeciesTree.relabel_clusters]; unfold relabelFamily
  simp only [Equiv.finsetCongr_apply, filter_map, sum_map]
  exact sum_congr (filter_congr fun C _ => by
      simp [Function.comp_apply, Equiv.finsetCongr_apply, map_eq_univ_iff, map_compl_eq])
    fun C _ => SpeciesTree.relabel_length_map σ e C

theorem SpeciesTree.sameUnrootedMetricTree_relabel_iff (σ σ' : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).SameUnrootedMetricTree (σ'.relabel e) ↔ σ.SameUnrootedMetricTree σ' := by
  unfold SpeciesTree.SameUnrootedMetricTree
  simp only [SpeciesTree.relabel_clusters, unroot_relabelFamily]
  refine and_congr (relabelFamily_injective e).eq_iff ⟨fun h A hA hA2 hAc2 => ?_, fun h B hB hB2 hBc2 => ?_⟩
  · simpa [SpeciesTree.unrootedLength_relabel] using h (A.map e.toEmbedding)
      (by simpa [relabelFamily, mem_map_equiv, Equiv.finsetCongr_symm] using hA)
      (by rwa [card_map]) (by rwa [map_compl_eq, card_map])
  · obtain ⟨A, hA, rfl⟩ := mem_map.1 hB
    simp only [Function.Embedding.coeFn_mk, Equiv.finsetCongr_apply, SpeciesTree.unrootedLength_relabel]
    exact h A hA (by simpa using hB2) (by simpa [map_compl_eq] using hBc2)

end Relabel

variable {X : Type*} [Fintype X] [DecidableEq X]

def U4 : ℕ → Finset (Finset (Fin 4))
  | 1 => treeOfClusters {{0, 1}}
  | _ => treeOfClusters ∅

def U5 : ℕ → Finset (Finset (Fin 5))
  | 2 => treeOfClusters {{0, 1}, {3, 4}}
  | 1 => treeOfClusters {{0, 1}}
  | _ => treeOfClusters ∅

theorem by_unrootB {τ : SpeciesTree X} {U : Finset (Finset X)}
    (P : Finset (Finset X) → Bool)
    (hdec : ∀ N ∈ (U.filter (fun A => 2 ≤ #A)).powerset,
      (∀ A ∈ N, ∀ B ∈ N, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) →
      (∀ A ∈ U.filter (fun A => 2 ≤ #A ∧ 2 ≤ #Aᶜ), A ∈ N ∨ Aᶜ ∈ N) → P (hierarchyOf N) = true)
    (h : unroot τ.clusters = U) : P τ.clusters = true := by
  rw [show τ.clusters = hierarchyOf (τ.clusters.filter fun A => 2 ≤ #A ∧ A ≠ univ) by
    ext A; simp only [hierarchyOf, mem_insert, mem_union, mem_image, mem_univ, true_and, mem_filter]
    refine ⟨fun hA => ?_, fun h' => ?_⟩
    · by_cases hu : A = univ; · exact Or.inl hu
      by_cases h2 : 2 ≤ #A; · exact Or.inr (Or.inl ⟨hA, h2, hu⟩)
      obtain ⟨x, rfl⟩ := card_eq_one.1 (show #A = 1 by have := (τ.nonempty_of_mem A hA).card_pos; omega)
      exact Or.inr (Or.inr ⟨x, rfl⟩)
    · rcases h' with rfl | ⟨hA, -⟩ | ⟨x, rfl⟩; exacts [τ.univ_mem, hA, τ.singleton_mem x]]
  refine hdec _ (mem_powerset.2 fun A hA => ?_)
    (fun A hA B hB => τ.laminar A (mem_filter.1 hA).1 B (mem_filter.1 hB).1) fun A hA => ?_
  · obtain ⟨h1, h2, h3⟩ := mem_filter.1 hA
    exact mem_filter.2 ⟨h ▸ mem_unroot.2 (Or.inl ⟨h1, h3⟩), h2⟩
  · obtain ⟨hAU, h2, h2c⟩ := mem_filter.1 hA
    rcases mem_unroot.1 (h ▸ hAU) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩
    · exact Or.inl (mem_filter.2 ⟨h1, h2, h1'⟩)
    · exact Or.inr (mem_filter.2 ⟨h1, h2c, h1'⟩)

theorem unroot_compat (σ : SpeciesTree X) {A B : Finset X}
    (hA : A ∈ unroot σ.clusters) (hB : B ∈ unroot σ.clusters) :
    Disjoint A B ∨ Disjoint A Bᶜ ∨ Disjoint Aᶜ B ∨ Disjoint Aᶜ Bᶜ := by
  let P (U V : Finset X) := Disjoint U V ∨ Disjoint U Vᶜ ∨ Disjoint Uᶜ V ∨ Disjoint Uᶜ Vᶜ
  have cl : ∀ {U V}, U ∈ σ.clusters → V ∈ σ.clusters → P U V := fun hU hV =>
    (σ.laminar _ hU _ hV).elim (Or.inr ∘ Or.inl ∘ disjoint_compl_right_iff.2) fun h =>
      h.elim (Or.inr ∘ Or.inr ∘ Or.inl ∘ disjoint_compl_left_iff.2) Or.inl
  have pc : ∀ {U V}, P Uᶜ V → P U V := fun h => by dsimp only [P] at h ⊢; rw [compl_compl] at h; tauto
  have qc : ∀ {U V}, P U Vᶜ → P U V := fun h => by dsimp only [P] at h ⊢; rw [compl_compl] at h; tauto
  rcases mem_unroot.1 hA with ⟨hA', -⟩ | ⟨hA', -⟩ <;> rcases mem_unroot.1 hB with ⟨hB', -⟩ | ⟨hB', -⟩
  exacts [cl hA' hB', qc (cl hA' hB'), pc (cl hA' hB'), pc (qc (cl hA' hB'))]

lemma normal_form {n : ℕ} (hn : n = 4 ∨ n = 5) (hX : Fintype.card X = n)
    (σ : SpeciesTree X) (U : ℕ → Finset (Finset (Fin n))) (ks : Finset ℕ)
    (hU : ∀ k ∈ ks, ∀ A ∈ (univ : Finset (Finset (Fin n))),
      A ∈ U k ↔ #A = 1 ∨ #A = n - 1 ∨
        A ∈ (U k).filter (fun B => #B = 2) ∨ Aᶜ ∈ (U k).filter (fun B => #B = 2))
    (horb : ∀ P ∈ ((univ : Finset (Finset (Fin n))).filter (fun A => #A = 2)).powerset,
      (∀ A ∈ P, n = 4 → Aᶜ ∈ P) →
      (∀ A ∈ P, ∀ B ∈ P, Disjoint A B ∨ Disjoint A Bᶜ ∨ Disjoint Aᶜ B ∨ Disjoint Aᶜ Bᶜ) →
      ∃ g ∈ (univ : Finset (Equiv.Perm (Fin n))), ∃ k ∈ ks,
        relabelFamily g P = (U k).filter (fun A => #A = 2)) :
    ∃ e : Fin n ≃ X, ∃ k ∈ ks, unroot (σ.relabel e.symm).clusters = U k := by
  let e₀ := Fintype.equivFinOfCardEq hX
  let τ₀ := σ.relabel e₀
  obtain ⟨g, -, k, hk, hg⟩ := horb
    ((unroot τ₀.clusters).filter fun A => #A = 2)
    (mem_powerset.2 fun A hA => mem_filter.2 ⟨mem_univ A, (mem_filter.1 hA).2⟩)
    (fun A hA hn4 => mem_filter.2 ⟨compl_mem_unroot.2 (mem_filter.1 hA).1,
      by rw [card_compl, Fintype.card_fin, (mem_filter.1 hA).2, hn4]⟩)
    (fun _ hA _ hB => unroot_compat _ (mem_filter.1 hA).1 (mem_filter.1 hB).1)
  let ρ := τ₀.relabel g
  refine ⟨g.symm.trans e₀.symm, k, hk, ?_⟩
  rw [show (σ.relabel (g.symm.trans e₀.symm).symm).clusters = ρ.clusters by
    show relabelFamily (e₀.trans g) σ.clusters = relabelFamily g (relabelFamily e₀ σ.clusters)
    simp [relabelFamily, ← Equiv.finsetCongr_trans]]
  have hP : (unroot ρ.clusters).filter (fun B => #B = 2) = (U k).filter (fun B => #B = 2) := by
    rw [← hg, show ρ.clusters = relabelFamily g τ₀.clusters from rfl, unroot_relabelFamily]
    unfold relabelFamily; simp only [Equiv.finsetCongr_apply, filter_map]
    exact congrArg _ (filter_congr fun _ _ => by simp)
  have hsing : ∀ x : Fin n, {x} ∈ unroot ρ.clusters := fun x =>
    mem_unroot.2 (Or.inl ⟨ρ.singleton_mem x, fun e => by have := congrArg card e; simp at this; omega⟩)
  ext A; rw [hU k hk A (mem_univ A), ← hP]
  constructor
  · intro h
    obtain ⟨c1, c2⟩ := nonempty_of_mem_unroot ρ.isHierarchy h
    have hc1 := card_pos.2 c1; have hc2 := (card_lt_iff_ne_univ A).2 c2
    rw [Fintype.card_fin] at hc2
    have hcc : #Aᶜ = n - #A := by rw [card_compl, Fintype.card_fin]
    rcases (by omega : #A = 1 ∨ #A = n - 1 ∨ #A = 2 ∨ #Aᶜ = 2) with h1 | h1 | h1 | h1
    exacts [Or.inl h1, Or.inr (Or.inl h1), Or.inr (Or.inr (Or.inl (mem_filter.2 ⟨h, h1⟩))),
      Or.inr (Or.inr (Or.inr (mem_filter.2 ⟨compl_mem_unroot.2 h, h1⟩)))]
  · rintro (h1 | h1 | h1 | h1)
    · obtain ⟨x, rfl⟩ := card_eq_one.1 h1; exact hsing x
    · obtain ⟨x, hx⟩ := card_eq_one.1 (show #Aᶜ = 1 by rw [card_compl, Fintype.card_fin]; omega)
      exact compl_mem_unroot.1 (hx ▸ hsing x)
    · exact (mem_filter.1 h1).1
    · exact compl_mem_unroot.1 (mem_filter.1 h1).1

section Decide

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype
set_option synthInstance.maxSize 2000

theorem exists_equiv_unroot_eq_U4 (hX : Fintype.card X = 4) (σ : SpeciesTree X) :
    ∃ e : Fin 4 ≃ X, ∃ k ∈ ({0, 1} : Finset ℕ), unroot (σ.relabel e.symm).clusters = U4 k :=
  normal_form (Or.inl rfl) hX σ U4 {0, 1} (by decide +kernel) (by decide +kernel)

theorem exists_equiv_unroot_eq_U5 (hX : Fintype.card X = 5) (σ : SpeciesTree X) :
    ∃ e : Fin 5 ≃ X, ∃ k ∈ ({0, 1, 2} : Finset ℕ), unroot (σ.relabel e.symm).clusters = U5 k :=
  normal_form (Or.inr rfl) hX σ U5 {0, 1, 2} (by decide +kernel) (by decide +kernel)

end Decide

end ADR11
