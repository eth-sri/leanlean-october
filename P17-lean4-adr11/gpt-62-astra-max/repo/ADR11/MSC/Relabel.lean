module
public import ADR11.MSC.Marginal
public import ADR11.MSC.MultiSample

/-! Relabelling is the special case of extension with one sample in each
fibre. Naturality then follows from consistency under lineage sampling. -/
@[expose] public section
namespace ADR11
open Finset
variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

private theorem map_compl_aux (e : X ≃ Y) (A : Finset X) :
    (A.map e.toEmbedding)ᶜ = Aᶜ.map e.toEmbedding := by aesop

private theorem map_full (e : X ≃ Y) (A : Finset X) : A.map e.toEmbedding = univ ↔ A = univ := by
  rw [← map_univ_equiv e, map_inj]

def relabelFamily (e : X ≃ Y) (F : Clusters X) := F.image (Finset.map e.toEmbedding)

theorem unroot_relabelFamily (e : X ≃ Y) (F : Clusters X) : unroot (relabelFamily e F) = relabelFamily e (unroot F) := by
  unfold relabelFamily unroot
  rw [← map_univ_equiv e, ← image_erase (map_injective e.toEmbedding),image_union,image_image,image_image]
  congr 2; funext A; exact map_compl_aux e A

noncomputable abbrev SpeciesTree.relabel (σ : SpeciesTree X) (e : X ≃ Y) := σ.extend e.symm.surjective

private theorem pre_map (e : X ≃ Y) (A : Finset X) : pre e.symm A = A.map e.toEmbedding := by aesop

theorem SpeciesTree.relabel_clusters (σ : SpeciesTree X) (e : X ≃ Y) : (σ.relabel e).clusters = relabelFamily e σ.clusters := by
  change σ.traces e.symm = _; rw [traces_of_injective _ _ e.symm.injective,project]
  simp only [funext (pre_map e), map_nonempty,filter_eq_self.mpr σ.nonempty_of_mem,relabelFamily]

@[simp] theorem SpeciesTree.relabel_length_map (σ : SpeciesTree X) (e : X ≃ Y) {A : Finset X} (ha : A ∈ σ.clusters) :
    (σ.relabel e).length (A.map e.toEmbedding) = σ.length A := by
  rw [← pre_map,relabel,extend,σ.pull_time ha]; simp [fiber,sum_filter,(pre_injective e.symm.surjective).eq_iff,ha]

theorem SpeciesTree.binary_relabel {σ : SpeciesTree X} (h : σ.IsBinary) (e : X ≃ Y) : (σ.relabel e).IsBinary := by
  intro B hb h2; rw [relabel_clusters] at hb ⊢
  obtain ⟨A,ha,rfl⟩ := mem_image.mp hb
  obtain ⟨C,hc,D,hd,dis,u⟩ := h A ha (by simpa using h2)
  exact ⟨_,mem_image_of_mem _ hc,_,mem_image_of_mem _ hd,(disjoint_map _).mpr dis, by rw [←map_union,u]⟩

theorem SpeciesTree.unrootedDist_relabel_eq_iff (σ τ : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).unrootedDist id = (τ.relabel e).unrootedDist id ↔ σ.unrootedDist id = τ.unrootedDist id := by
  simp only [relabel,extend,unrootedDist_pull]
  have he : e.symm ∘ e.toEmbedding = id := funext e.symm_apply_apply
  exact ⟨fun h => he ▸ sample_eq h e.toEmbedding, fun h => sample_eq h e.symm.toEmbedding⟩

theorem SpeciesTree.sameRootedMetricTree_relabel_iff (σ τ : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).SameRootedMetricTree (τ.relabel e) ↔ σ.SameRootedMetricTree τ := by
  simp only [SameRootedMetricTree,relabel_clusters,relabelFamily, (image_injective (map_injective e.toEmbedding)).eq_iff,
    forall_mem_image,card_map,ne_eq,map_full,and_congr_right_iff]
  intro h; simp +contextual [← h,relabel_length_map]

theorem SpeciesTree.unrootedLength_relabel (σ : SpeciesTree X) (e : X ≃ Y) (A : Finset X) :
    (σ.relabel e).unrootedLength (A.map e.toEmbedding) = σ.unrootedLength A := by
  unfold unrootedLength; rw [relabel_clusters]; unfold relabelFamily
  rw [filter_image,sum_image fun _ _ _ _ h => map_injective _ h]; simp [map_full,map_compl_aux]; apply sum_congr rfl; intro A ha; exact σ.relabel_length_map e (mem_filter.mp ha).1

theorem SpeciesTree.sameUnrootedMetricTree_relabel_iff (σ τ : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).SameUnrootedMetricTree (τ.relabel e) ↔ σ.SameUnrootedMetricTree τ := by
  simp only [SameUnrootedMetricTree,relabel_clusters,unroot_relabelFamily]
  simp only [relabelFamily, (image_injective (map_injective e.toEmbedding)).eq_iff,
    forall_mem_image,card_map,map_compl_aux,unrootedLength_relabel]

end ADR11
