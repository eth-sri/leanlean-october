module

public import ADR11.MSC.Basic
/-!
# Relabelling taxa

Everything in the model is natural with respect to bijections of the taxa: relabelling a species
tree relabels its gene tree distributions.

* `relabelFamily e F`: the image of a family of clusters under a bijection `e : X ≃ Y`;
  `e.finsetCongr.finsetCongr`: the same map, as an equivalence.
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
variable {F : Family X} {A : Finset X}
variable (σ σ' : SpeciesTree X) (e : X ≃ Y)

/-- The image of a family of clusters under a bijection. -/
def relabelFamily (F : Family X) : Family Y :=
  F.image fun A => A.map e.toEmbedding

private lemma msc_map_compl (A : Finset X) :
    (A.map e.toEmbedding)ᶜ = Aᶜ.map e.toEmbedding := by
  ext y
  simp

private lemma msc_map_eq_univ_iff (A : Finset X) :
    A.map e.toEmbedding = univ ↔ A = univ := by
  rw [← Finset.map_univ_equiv e, Finset.map_inj]

theorem unroot_relabelFamily (F : Family X) :
    unroot (relabelFamily e F) = relabelFamily e (unroot F) := by
  unfold unroot relabelFamily
  rw [← Finset.map_univ_equiv e, ← Finset.image_erase (Finset.map_injective e.toEmbedding),
    image_union, image_image, image_image]
  congr 2
  funext A
  exact msc_map_compl e A

@[simp 1100] theorem relabelFamilyEquiv_apply (e : X ≃ Y) (F : Family X) :
    e.finsetCongr.finsetCongr F = relabelFamily e F := Finset.map_eq_image _ _

theorem map_mem_relabelFamily {e : X ≃ Y} :
    A.map e.toEmbedding ∈ relabelFamily e F ↔ A ∈ F := by
  simp_all [relabelFamily]

set_option backward.isDefEq.respectTransparency false in
/-- Kingman's coalescent is invariant under relabelling the lineages. -/
theorem kingmanTransition_relabelFamily (t : ℝ) (F G : Family X) :
    kingmanTransition t (relabelFamily e F) (relabelFamily e G) = kingmanTransition t F G := by
  have hQ : (kingmanGenerator (L := Y)).submatrix (e.finsetCongr.finsetCongr)
      (e.finsetCongr.finsetCongr) = kingmanGenerator (L := X) := by
    ext F G
    simp only [Matrix.submatrix_apply, relabelFamilyEquiv_apply]
    simp [kingmanGenerator, roots, relabelFamily, filter_image,
        (Finset.map_injective e.toEmbedding).eq_iff,
        ← Finset.map_union, ← image_insert, image_inj (Finset.map_injective e.toEmbedding)]
    rw [card_image_of_injective _ (Finset.map_injective e.toEmbedding)]
  open scoped Matrix.Norms.Operator in
  have h := NormedSpace.map_exp
    (Matrix.reindexRingEquiv ℝ (e.finsetCongr.finsetCongr).symm)
    (continuous_id.matrix_submatrix (e.finsetCongr.finsetCongr) (e.finsetCongr.finsetCongr))
    (t • kingmanGenerator (L := Y))
  simpa only [kingmanTransition, Matrix.coe_reindexRingEquiv, Matrix.reindex_apply,
    Equiv.symm_symm, Matrix.submatrix_smul, Pi.smul_apply, hQ, Matrix.submatrix_apply, relabelFamilyEquiv_apply] using
    congrArg (fun A => A F G) h

/-- The species tree `σ` with its taxa relabelled by `e`. -/
def SpeciesTree.relabel : SpeciesTree Y where
  clusters := relabelFamily e σ.clusters
  univ_mem := mem_image.2 ⟨univ, σ.univ_mem, Finset.map_univ_equiv e⟩
  singleton_mem := fun y => mem_image.2 ⟨{e.symm y}, σ.singleton_mem _, by simp⟩
  nonempty_of_mem := by simpa [relabelFamily] using σ.nonempty_of_mem
  laminar := by simpa [relabelFamily] using σ.laminar
  length B := σ.length (B.map e.symm.toEmbedding)
  length_pos := by
    simpa [relabelFamily, Finset.map_map, msc_map_eq_univ_iff] using σ.length_pos

@[simp] theorem SpeciesTree.relabel_clusters (σ : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).clusters = relabelFamily e σ.clusters := rfl

@[simp] theorem SpeciesTree.relabel_length_map (σ : SpeciesTree X) (e : X ≃ Y) (A : Finset X) :
    (σ.relabel e).length (A.map e.toEmbedding) = σ.length A := by
  simp [SpeciesTree.relabel, Finset.map_map]

theorem SpeciesTree.isBinary_relabel_iff :
    (σ.relabel e).IsBinary ↔ σ.IsBinary := by
  simp only [SpeciesTree.IsBinary, SpeciesTree.relabel_clusters, relabelFamily,
    forall_mem_image, exists_mem_image, Finset.card_map, Finset.disjoint_map,
    ← Finset.map_union, (Finset.map_injective e.toEmbedding).eq_iff]

/-- **Naturality of the multispecies coalescent.** Relabelling the taxa along `e` and the
lineages along `e` (compatibly with the sampling maps) relabels the distribution of the forest
leaving each population. -/
private theorem forestDist_relabel (A : Finset X) (G : Family X) :
    forestDist (σ.relabel e).clusters (σ.relabel e).length id
      (A.map e.toEmbedding) (relabelFamily e G) =
      forestDist σ.clusters σ.length id A G := by
  simp only [SpeciesTree.relabel_clusters]
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist.eq_1 (relabelFamily e σ.clusters), forestDist.eq_1 σ.clusters]
  have hch := childClusters_image (Finset.mapEmbedding e.toEmbedding) σ.clusters A
  change childClusters (relabelFamily e σ.clusters) (A.map e.toEmbedding) =
    relabelFamily e (childClusters σ.clusters A) at hch
  let ψ : childClusters σ.clusters A ≃ childClusters (relabelFamily e σ.clusters) (A.map e.toEmbedding) :=
    (Equiv.finsetCongr e).subtypeEquiv fun B => by
      rw [hch, Equiv.finsetCongr_apply, map_mem_relabelFamily]
  let Φ := ψ.arrowCongr (e.finsetCongr.finsetCongr)
  rw [← Φ.sum_comp]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hΦ : ∀ B : childClusters σ.clusters A, Φ f (ψ B) = relabelFamily e (f B) := fun B => by
    simp [Φ, Equiv.arrowCongr_apply]
  congr 1
  · rw [← ψ.prod_comp]
    refine Finset.prod_congr rfl fun B _ => ?_
    rw [hΦ]
    exact ih B (mem_childClusters.1 B.2).2.1 (f B)
  · have hsup : univ.sup (Φ f) = relabelFamily e (univ.sup f) := by
      rw [← sup_univ_equiv ψ]
      simp_rw [hΦ, relabelFamily, sup_eq_biUnion, biUnion_image]
    rw [hsup]
    have hsample : sampledForest id (A.map e.toEmbedding) = relabelFamily e (sampledForest id A) := by
      unfold sampledForest relabelFamily
      rw [← Finset.map_univ_equiv e, filter_map]
      simp [map_eq_image, image_image, Function.comp_def]
    rw [hsample]
    simp only [relabelFamily, ← image_union]
    change populationKernel (σ.relabel e).length (A.map e.toEmbedding)
      (relabelFamily e (univ.sup f ∪ sampledForest id A)) (relabelFamily e G) = _
    simp only [populationKernel, msc_map_eq_univ_iff, Matrix.ite_apply, SpeciesTree.relabel_length_map,
      kingmanAbsorption, kingmanTransition_relabelFamily]

theorem SpeciesTree.unrootedDist_relabel
    (T : Family X) :
    (σ.relabel e).unrootedDist id (relabelFamily e T) = σ.unrootedDist id T := by
  have hr := forestDist_relabel σ e univ
  simp only [Finset.map_univ_equiv] at hr
  grind [← (e.finsetCongr.finsetCongr).sum_comp, ← image_inj (Finset.map_injective e.toEmbedding), SpeciesTree.rootedDist, relabelFamily, ← relabelFamilyEquiv_apply, ← unroot_relabelFamily, SpeciesTree.unrootedDist]

theorem SpeciesTree.unrootedDist_relabel_eq_iff :
    (σ.relabel e).unrootedDist id = (σ'.relabel e).unrootedDist id ↔
      σ.unrootedDist id = σ'.unrootedDist id := by
  simp [funext_iff]
  rw [← (e.finsetCongr.finsetCongr).forall_congr_right]
  simp [SpeciesTree.unrootedDist_relabel]

theorem SpeciesTree.sameRootedMetricTree_relabel_iff :
    (σ.relabel e).SameRootedMetricTree (σ'.relabel e) ↔ σ.SameRootedMetricTree σ' := by
  simp only [SpeciesTree.SameRootedMetricTree, SpeciesTree.relabel_clusters,
    relabelFamily, image_inj (Finset.map_injective e.toEmbedding), forall_mem_image, SpeciesTree.relabel_length_map,
    Finset.card_map, ne_eq, msc_map_eq_univ_iff]

theorem SpeciesTree.unrootedLength_relabel (A : Finset X) :
    (σ.relabel e).unrootedLength (A.map e.toEmbedding) = σ.unrootedLength A := by
  unfold SpeciesTree.unrootedLength
  rw [SpeciesTree.relabel_clusters]
  unfold relabelFamily
  rw [filter_image, sum_image (Finset.map_injective e.toEmbedding).injOn]
  refine Finset.sum_congr (filter_congr fun C _ => ?_) fun C _ =>
    SpeciesTree.relabel_length_map σ e C
  simp only [ne_eq, msc_map_eq_univ_iff, Finset.map_inj, msc_map_compl]

end ADR11
