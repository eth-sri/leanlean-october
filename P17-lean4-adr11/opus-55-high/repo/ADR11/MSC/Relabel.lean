module

public import ADR11.MSC.Basic

/-!
# Relabelling taxa

Everything in the model is natural with respect to bijections of the taxa: relabelling a species
tree relabels its gene tree distributions.

* `relabelFamily e F`: the image of a family of clusters under a bijection `e : X ≃ Y`;
  `relabelFamilyEquiv e`: the same map, as an equivalence.
* `SpeciesTree.relabel σ e`: the species tree `σ` with taxa relabelled by `e`.

## Main results

* `kingmanGenerator_relabelFamily`, `kingmanTransition_relabelFamily`,
  `kingmanAbsorption_relabelFamily`: Kingman's coalescent is invariant under relabelling the
  lineages.
* `forestDist_relabel`: naturality of the multispecies coalescent under relabelling the taxa and
  the lineages; `forestDist_relabel_lineages`: relabelling the lineages only.
* `SpeciesTree.unrootedDist_relabel`, `SpeciesTree.rootedDist_relabel`: the gene tree
  distributions of the relabelled tree are the relabelled distributions.
* `SpeciesTree.sameRootedMetricTree_relabel_iff`, `SpeciesTree.sameUnrootedMetricTree_relabel_iff`:
  relabelling preserves and reflects equality of metric trees.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The image of a family of clusters under a bijection. -/
def relabelFamily (e : X ≃ Y) (F : Finset (Finset X)) : Finset (Finset Y) :=
  F.image fun A => A.map e.toEmbedding

lemma msc_map_symm_map (e : X ≃ Y) (A : Finset X) :
    (A.map e.toEmbedding).map e.symm.toEmbedding = A := by aesop

theorem msc_map_compl (e : X ≃ Y) (A : Finset X) :
    (A.map e.toEmbedding)ᶜ = Aᶜ.map e.toEmbedding := by aesop

lemma msc_map_map_symm (e : X ≃ Y) (B : Finset Y) :
    (B.map e.symm.toEmbedding).map e.toEmbedding = B := by aesop

lemma msc_map_eq_univ_iff (e : X ≃ Y) (A : Finset X) :
    A.map e.toEmbedding = univ ↔ A = univ := by
  rw [← Finset.map_univ_equiv e, Finset.map_inj]

theorem relabelFamily_injective (e : X ≃ Y) : Function.Injective (relabelFamily e) :=
  Finset.image_injective (Finset.map_injective e.toEmbedding)

theorem relabelFamily_symm (e : X ≃ Y) (F : Finset (Finset X)) :
    relabelFamily e.symm (relabelFamily e F) = F := by
  simp [relabelFamily, image_image, Function.comp_def, msc_map_symm_map]

theorem unroot_relabelFamily (e : X ≃ Y) (F : Finset (Finset X)) :
    unroot (relabelFamily e F) = relabelFamily e (unroot F) := by
  unfold unroot relabelFamily
  rw [← map_univ_equiv e, ← image_erase (map_injective _), image_union, image_image, image_image]
  simp [Function.comp_def, msc_map_compl]

/-- Relabelling families of clusters along `e`, as an equivalence. -/
def relabelFamilyEquiv (e : X ≃ Y) : Finset (Finset X) ≃ Finset (Finset Y) where
  toFun := relabelFamily e
  invFun := relabelFamily e.symm
  left_inv := relabelFamily_symm e
  right_inv := fun F => by simpa using relabelFamily_symm e.symm F

@[simp] theorem relabelFamilyEquiv_apply (e : X ≃ Y) (F : Finset (Finset X)) :
    relabelFamilyEquiv e F = relabelFamily e F := rfl

theorem mem_relabelFamily {e : X ≃ Y} {F : Finset (Finset X)} {B : Finset Y} :
    B ∈ relabelFamily e F ↔ B.map e.symm.toEmbedding ∈ F := by
  simp [relabelFamily, mem_image]
  exact ⟨fun ⟨A, hA, h⟩ => h ▸ by rwa [msc_map_symm_map], fun h => ⟨_, h, msc_map_map_symm e B⟩⟩

theorem map_mem_relabelFamily {e : X ≃ Y} {F : Finset (Finset X)} {A : Finset X} :
    A.map e.toEmbedding ∈ relabelFamily e F ↔ A ∈ F := by simp_all [relabelFamily]

theorem relabelFamily_union (e : X ≃ Y) (F G : Finset (Finset X)) :
    relabelFamily e (F ∪ G) = relabelFamily e F ∪ relabelFamily e G :=
  image_union _ _

section Kernels

variable {L : Type*} [Fintype L] [DecidableEq L] {M : Type*} [Fintype M] [DecidableEq M]

theorem roots_relabelFamily (e : L ≃ M) (F : Finset (Finset L)) :
    roots (relabelFamily e F) = relabelFamily e (roots F) := by
  simp [roots, relabelFamily, filter_image]

theorem card_relabelFamily (e : L ≃ M) (F : Finset (Finset L)) :
    #(relabelFamily e F) = #F :=
  card_image_of_injective _ (Finset.map_injective e.toEmbedding)

/-- The generator of Kingman's coalescent is invariant under relabelling the lineages. -/
theorem kingmanGenerator_relabelFamily (e : L ≃ M) (F G : Finset (Finset L)) :
    kingmanGenerator (relabelFamily e F) (relabelFamily e G) = kingmanGenerator F G := by
  unfold kingmanGenerator
  rw [roots_relabelFamily, card_relabelFamily]
  refine if_congr (relabelFamily_injective e).eq_iff rfl (if_congr ?_ rfl rfl)
  simp [relabelFamily, exists_mem_image, ne_eq, map_inj, ← map_union, ← image_insert,
    (image_injective (map_injective e.toEmbedding)).eq_iff]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
/-- Kingman's coalescent is invariant under relabelling the lineages. -/
theorem kingmanTransition_relabelFamily (e : L ≃ M) (t : ℝ) (F G : Finset (Finset L)) :
    kingmanTransition t (relabelFamily e F) (relabelFamily e G) = kingmanTransition t F G := by
  have h : (t • kingmanGenerator (L := M)).submatrix (relabelFamilyEquiv e)
      (relabelFamilyEquiv e) = t • kingmanGenerator := by
    ext F G
    simp [kingmanGenerator_relabelFamily]
  unfold kingmanTransition
  rw [← h]
  exact congrFun₂ (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℝ ℝ (relabelFamilyEquiv e).symm)
    (continuous_id.matrix_submatrix _ _) _) F G

theorem kingmanAbsorption_relabelFamily (e : L ≃ M) (F G : Finset (Finset L)) :
    kingmanAbsorption (relabelFamily e F) (relabelFamily e G) = kingmanAbsorption F G := by
  unfold kingmanAbsorption
  simp_rw [kingmanTransition_relabelFamily]

end Kernels

section Naturality

variable {L : Type*} [Fintype L] [DecidableEq L] {M : Type*} [Fintype M] [DecidableEq M]

theorem childClusters_relabelFamily (e : X ≃ Y) (H : Finset (Finset X)) (A : Finset X) :
    childClusters (relabelFamily e H) (A.map e.toEmbedding) =
      relabelFamily e (childClusters H A) := by
  simp [childClusters, relabelFamily, filter_image]

theorem sampledForest_relabel (e : X ≃ Y) (eL : L ≃ M) {s : L → X} {s' : M → Y}
    (hs : ∀ l, s' (eL l) = e (s l)) (A : Finset X) :
    sampledForest s' (A.map e.toEmbedding) = relabelFamily eL (sampledForest s A) := by
  obtain rfl : s' = e ∘ s ∘ eL.symm := funext fun m => by simp [← hs]
  ext C
  rw [mem_relabelFamily]
  simp [mem_sampledForest, eL.exists_congr_left, Function.comp_apply, mem_map_equiv, Equiv.symm_apply_apply]
  exact exists_congr fun l => and_congr_right fun _ => ⟨fun h => by simp [← h], fun h => by rw [← msc_map_map_symm eL C, ← h]; simp⟩

lemma msc_relabelFamily_sup {ι : Type*} [Fintype ι] (eL : L ≃ M)
    (f : ι → Finset (Finset L)) :
    relabelFamily eL (univ.sup f) = univ.sup (fun i => relabelFamily eL (f i)) := by aesop (add simp [relabelFamily])

lemma msc_sup_univ_equiv {ι κ α : Type*} [Fintype ι] [Fintype κ] [SemilatticeSup α]
    [OrderBot α] (ψ : ι ≃ κ) (g : κ → α) :
    univ.sup (fun i => g (ψ i)) = univ.sup g := by
  conv_rhs => rw [← Finset.map_univ_equiv ψ, Finset.sup_map]
  rfl

theorem populationKernel_relabel (e : X ≃ Y) (eL : L ≃ M)
    {len : Finset X → ℝ} {len' : Finset Y → ℝ} (hlen : ∀ A, len' (A.map e.toEmbedding) = len A)
    (A : Finset X) (F G : Finset (Finset L)) :
    populationKernel len' (A.map e.toEmbedding) (relabelFamily eL F) (relabelFamily eL G) =
      populationKernel len A F G := by
  simp [populationKernel, msc_map_eq_univ_iff, hlen]
  split_ifs
  exacts [kingmanAbsorption_relabelFamily eL F G, kingmanTransition_relabelFamily eL _ F G]

/-- **Naturality of the multispecies coalescent.** Relabelling the taxa along `e` and the
lineages along `eL` (compatibly with the sampling maps) relabels the distribution of the forest
leaving each population. -/
theorem forestDist_relabel (e : X ≃ Y) (eL : L ≃ M) (H : Finset (Finset X))
    {len : Finset X → ℝ} {len' : Finset Y → ℝ} (hlen : ∀ A, len' (A.map e.toEmbedding) = len A)
    {s : L → X} {s' : M → Y} (hs : ∀ l, s' (eL l) = e (s l)) (A : Finset X)
    (G : Finset (Finset L)) :
    forestDist (relabelFamily e H) len' s' (A.map e.toEmbedding) (relabelFamily eL G) =
      forestDist H len s A G := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist.eq_1 (relabelFamily e H), forestDist.eq_1 H]
  let ψ : childClusters H A ≃ childClusters (relabelFamily e H) (A.map e.toEmbedding) :=
    (Equiv.finsetCongr e).subtypeEquiv fun B => by
      rw [childClusters_relabelFamily e H A, Equiv.finsetCongr_apply, map_mem_relabelFamily]
  let Φ := ψ.arrowCongr (relabelFamilyEquiv eL)
  rw [← Φ.sum_comp]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hΦ : ∀ B : childClusters H A, Φ f (ψ B) = relabelFamily eL (f B) := fun B => by
    simp [Φ, Equiv.arrowCongr_apply]
  have hψ : ∀ B : childClusters H A,
      ((ψ B : childClusters (relabelFamily e H) (A.map e.toEmbedding)) : Finset Y) =
        (B : Finset X).map e.toEmbedding := fun B => rfl
  congr 1
  · rw [← ψ.prod_comp]
    refine Finset.prod_congr rfl fun B _ => ?_
    rw [hΦ, hψ]
    exact ih B (mem_childClusters.1 B.2).2.1 (f B)
  · have hsup : univ.sup (Φ f) = relabelFamily eL (univ.sup f) := by
      rw [msc_relabelFamily_sup, ← msc_sup_univ_equiv ψ]
      simp [hΦ]
    rw [hsup, sampledForest_relabel e eL hs, ← relabelFamily_union]
    exact populationKernel_relabel e eL hlen A _ G

end Naturality

/-- The species tree `σ` with its taxa relabelled by `e`. -/
def SpeciesTree.relabel (σ : SpeciesTree X) (e : X ≃ Y) : SpeciesTree Y where
  clusters := relabelFamily e σ.clusters
  univ_mem := mem_image.2 ⟨univ, σ.univ_mem, map_univ_equiv e⟩
  singleton_mem y := mem_image.2 ⟨{e.symm y}, σ.singleton_mem _, by simp⟩
  nonempty_of_mem := by simpa [relabelFamily] using σ.nonempty_of_mem
  laminar := by
    simp [relabelFamily, forall_mem_image, map_subset_map, disjoint_map]
    exact σ.laminar
  length B := σ.length (B.map e.symm.toEmbedding)
  length_pos := by
    simp [relabelFamily, forall_mem_image, msc_map_symm_map, ne_eq, msc_map_eq_univ_iff]
    exact σ.length_pos

@[simp] theorem SpeciesTree.relabel_clusters (σ : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).clusters = relabelFamily e σ.clusters := rfl

theorem SpeciesTree.relabel_length (σ : SpeciesTree X) (e : X ≃ Y) (B : Finset Y) :
    (σ.relabel e).length B = σ.length (B.map e.symm.toEmbedding) := rfl

@[simp] theorem SpeciesTree.relabel_length_map (σ : SpeciesTree X) (e : X ≃ Y) (A : Finset X) :
    (σ.relabel e).length (A.map e.toEmbedding) = σ.length A := by
  rw [SpeciesTree.relabel_length, msc_map_symm_map]

/-- Relabelling back along `e.symm` gives the original species tree. -/
theorem SpeciesTree.relabel_relabel_symm (σ : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).relabel e.symm = σ := by
  cases σ
  simp [SpeciesTree.relabel, relabelFamily_symm, msc_map_symm_map]

theorem SpeciesTree.isBinary_relabel_iff (σ : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).IsBinary ↔ σ.IsBinary := by
  unfold SpeciesTree.IsBinary
  simp [relabelFamily, ← map_union]

theorem SpeciesTree.rootedDist_relabel (σ : SpeciesTree X) (e : X ≃ Y) (G : Finset (Finset X)) :
    (σ.relabel e).rootedDist id (relabelFamily e G) = σ.rootedDist id G := by
  unfold SpeciesTree.rootedDist
  have := forestDist_relabel e e σ.clusters (len := σ.length) (len' := (σ.relabel e).length)
    (σ.relabel_length_map e) (s := id) (s' := id) (fun _ => rfl) univ G
  rwa [Finset.map_univ_equiv] at this

theorem SpeciesTree.unrootedDist_relabel (σ : SpeciesTree X) (e : X ≃ Y)
    (T : Finset (Finset X)) :
    (σ.relabel e).unrootedDist id (relabelFamily e T) = σ.unrootedDist id T := by
  unfold SpeciesTree.unrootedDist
  rw [← (relabelFamilyEquiv e).sum_comp]
  simp [unroot_relabelFamily, (relabelFamily_injective e).eq_iff, SpeciesTree.rootedDist_relabel]

theorem SpeciesTree.unrootedDist_relabel_eq_iff (σ σ' : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).unrootedDist id = (σ'.relabel e).unrootedDist id ↔
      σ.unrootedDist id = σ'.unrootedDist id := by
  rw [funext_iff, funext_iff, ← (relabelFamilyEquiv e).forall_congr_right]
  simp [SpeciesTree.unrootedDist_relabel]

theorem SpeciesTree.sameRootedMetricTree_relabel_iff (σ σ' : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).SameRootedMetricTree (σ'.relabel e) ↔ σ.SameRootedMetricTree σ' := by
  unfold SpeciesTree.SameRootedMetricTree
  rw [SpeciesTree.relabel_clusters, SpeciesTree.relabel_clusters, (relabelFamily_injective e).eq_iff]
  simp [relabelFamily, msc_map_eq_univ_iff]

theorem SpeciesTree.unrootedLength_relabel (σ : SpeciesTree X) (e : X ≃ Y) (A : Finset X) :
    (σ.relabel e).unrootedLength (A.map e.toEmbedding) = σ.unrootedLength A := by
  unfold SpeciesTree.unrootedLength
  simp [relabelFamily, filter_image, sum_image, msc_map_eq_univ_iff, msc_map_compl]

theorem SpeciesTree.sameUnrootedMetricTree_relabel_iff (σ σ' : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).SameUnrootedMetricTree (σ'.relabel e) ↔ σ.SameUnrootedMetricTree σ' := by
  unfold SpeciesTree.SameUnrootedMetricTree
  rw [SpeciesTree.relabel_clusters, SpeciesTree.relabel_clusters, unroot_relabelFamily, unroot_relabelFamily, (relabelFamily_injective e).eq_iff]
  simp [relabelFamily, msc_map_compl, SpeciesTree.unrootedLength_relabel]

end ADR11
