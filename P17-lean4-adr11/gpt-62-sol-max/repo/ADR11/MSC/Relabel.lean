module

public import ADR11.MSC.Independent
public import ADR11.Trees.Hierarchy

@[expose] public section

namespace ADR11
open Finset Independent
open scoped Independent
variable {X Y : Type*}

/-- Transport a cluster family along a bijection of its leaves. -/
def relabelFamily (e : X ≃ Y) : ClusterFamily X ≃ ClusterFamily Y := e.finsetCongr.finsetCongr

@[local simp] theorem map_mem_relabel {e : X ≃ Y} {A : Finset X} {F : ClusterFamily X} :
    A.map e.toEmbedding ∈ relabelFamily e F ↔ A ∈ F := mem_map' e.finsetCongr.toEmbedding

variable [DecidableEq Y]

theorem relabel_image (e : X ≃ Y) (F : ClusterFamily X) :
    relabelFamily e F = F.image (Finset.map e.toEmbedding) := map_eq_image e.finsetCongr.toEmbedding F

theorem forest_relabelled (e : X ≃ Y) {F : ClusterFamily X} (hF : IsForest F) :
    IsForest (relabelFamily e F) := by
  simpa only [IsForest, relabel_image, forall_mem_image, map_nonempty, map_subset_map, disjoint_map] using hF

variable [Fintype X] [Fintype Y] [DecidableEq X]

private theorem relabel_compl (e : X ≃ Y) (A : Finset X) :
    (A.map e.toEmbedding)ᶜ = Aᶜ.map e.toEmbedding := by
  ext; simp [mem_map_equiv]

omit [DecidableEq X] [DecidableEq Y] in
@[local simp] theorem relabel_univ (e : X ≃ Y) (A : Finset X) : A.map e.toEmbedding = univ ↔ A = univ := by
  rw [← map_univ_equiv e, map_inj]

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
@[local simp] theorem relabel_symm_map (e : X ≃ Y) (A : Finset X) :
    (A.map e.toEmbedding).map e.symm.toEmbedding = A := e.finsetCongr.symm_apply_apply A

theorem unroot_relabelFamily (e : X ≃ Y) (F : ClusterFamily X) :
    unroot (relabelFamily e F) = relabelFamily e (unroot F) := by
  ext B
  obtain ⟨A, rfl⟩ := e.finsetCongr.surjective B
  simp [mem_unroot, relabel_compl]

private theorem roots_relabel (e : X ≃ Y) (F : ClusterFamily X) :
    roots (relabelFamily e F) = relabelFamily e (roots F) := by
  simp [roots, relabel_image, filter_image, map_subset_map, map_inj]

private theorem relabel_generator_action (e : X ≃ Y) {F : ClusterFamily X}
    (u : ClusterFamily Y → ℝ) :
    ∑ G, kingmanGenerator F G * u (relabelFamily e G) = ∑ G, kingmanGenerator (relabelFamily e F) G * u G := by
  rw [← (relabelFamily e).sum_comp]
  refine sum_congr rfl fun G _ => congrArg (· * u (relabelFamily e G)) ?_
  simp only [kingmanGenerator, roots_relabel, (relabelFamily e).injective.eq_iff,
    show #(relabelFamily e (roots F)) = #(roots F) from card_map _]
  congr 1
  simp only [relabel_image, exists_mem_image, ne_eq, map_inj, ← map_union, ← image_insert,
    (image_injective (map_injective e.toEmbedding)).eq_iff]

/-- The same tree, with leaves renamed by `e`. -/
def SpeciesTree.relabel (σ : SpeciesTree X) (e : X ≃ Y) : SpeciesTree Y where
  clusters := relabelFamily e σ.clusters
  univ_mem := by simpa using (map_mem_relabel (e := e) (A := univ)).2 σ.univ_mem
  singleton_mem y := by simpa using (map_mem_relabel (e := e) (A := {e.symm y})).2 (σ.singleton_mem _)
  nonempty_of_mem := (forest_relabelled e σ.isHierarchy.2.2).1
  laminar := (forest_relabelled e σ.isHierarchy.2.2).2
  length B := σ.length (B.map e.symm.toEmbedding)
  length_pos := by simpa only [relabel_image, forall_mem_image, ne_eq, relabel_univ, relabel_symm_map] using σ.length_pos

@[simp] theorem SpeciesTree.relabel_clusters (σ : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).clusters = relabelFamily e σ.clusters := rfl

@[local simp] theorem relabel_length (σ : SpeciesTree X) (e : X ≃ Y) (A : Finset X) :
    (σ.relabel e).length (A.map e.toEmbedding) = σ.length A := congrArg σ.length (relabel_symm_map e A)

private theorem forest_relabel (σ : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).rootedDist id = pushD (relabelFamily e) (σ.rootedDist id) := by
  let f : ClusterFamily X →* ClusterFamily Y :=
    { toFun := relabelFamily e, map_one' := map_empty _, map_mul' := map_union }
  have h := forestDist_push f e.finsetCongr.toEmbedding σ.isHierarchy
    (s := id) (s' := id) (H' := (σ.relabel e).clusters) (len' := (σ.relabel e).length)
    (fun B => by
      change relabelFamily e (sampledForest id B) = sampledForest id (B.map e.toEmbedding)
      simp only [sampledForest, id_eq, filter_mem_eq_inter, univ_inter, relabel_image, map_eq_image, image_image]
      congr 1)
    (fun B _ => Or.inl (by
      change childClusters (relabelFamily e σ.clusters) (B.map e.toEmbedding) =
        (childClusters σ.clusters B).image (Finset.map e.toEmbedding)
      simp [childClusters, relabel_image, filter_image, map_ssubset_map]))
    (fun B _ F hF => population_push (relabelFamily e) (fun _ => relabel_generator_action e) hF
      (forest_relabelled e hF) (relabel_univ e B) (relabel_length σ e B)) σ.univ_mem
  simp only [show e.finsetCongr.toEmbedding univ = univ from map_univ_equiv e] at h
  exact h.symm

theorem SpeciesTree.unrootedDist_relabel (σ : SpeciesTree X) (e : X ≃ Y) (T : ClusterFamily X) :
    (σ.relabel e).unrootedDist id (relabelFamily e T) = σ.unrootedDist id T := by
  change pushD unroot _ _ = pushD unroot _ _
  rw [forest_relabel, pushD_comp, show unroot ∘ relabelFamily e = relabelFamily e ∘ unroot from
    funext (unroot_relabelFamily e), ← pushD_comp, pushD_equiv, Equiv.symm_apply_apply]

theorem SpeciesTree.unrootedDist_relabel_eq_iff (σ τ : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).unrootedDist id = (τ.relabel e).unrootedDist id ↔ σ.unrootedDist id = τ.unrootedDist id := by
  rw [funext_iff, funext_iff, (relabelFamily e).symm.forall_congr_left]
  simp only [Equiv.symm_symm, SpeciesTree.unrootedDist_relabel]

theorem SpeciesTree.isBinary_relabel (σ : SpeciesTree X) (e : X ≃ Y) (h : σ.IsBinary) :
    (σ.relabel e).IsBinary := by
  simpa only [SpeciesTree.IsBinary, relabel_clusters, relabel_image, forall_mem_image, exists_mem_image,
    card_map, disjoint_map, ← map_union, map_inj] using h

theorem SpeciesTree.sameRootedMetricTree_relabel_iff (σ τ : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).SameRootedMetricTree (τ.relabel e) ↔ σ.SameRootedMetricTree τ := by
  simp only [SameRootedMetricTree, relabel_clusters, (relabelFamily e).injective.eq_iff]
  simp only [relabel_image, forall_mem_image, card_map, ne_eq, relabel_univ, relabel_length]

private theorem length_relabel (σ : SpeciesTree X) (e : X ≃ Y) (A : Finset X) :
    (σ.relabel e).unrootedLength (A.map e.toEmbedding) = σ.unrootedLength A := by
  simp only [SpeciesTree.unrootedLength, SpeciesTree.relabel_clusters, relabel_image, filter_image,
    sum_image (fun _ _ _ _ h => map_injective e.toEmbedding h), ne_eq, relabel_univ, map_inj, relabel_compl,
    relabel_length]

theorem SpeciesTree.sameUnrootedMetricTree_relabel_iff (σ τ : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).SameUnrootedMetricTree (τ.relabel e) ↔ σ.SameUnrootedMetricTree τ := by
  simp only [SameUnrootedMetricTree, relabel_clusters, unroot_relabelFamily, (relabelFamily e).injective.eq_iff]
  simp only [relabel_image, forall_mem_image, relabel_compl, card_map, length_relabel]

end ADR11
