import RequestProject.DiskAttachmentRadialCore
import Mathlib.Topology.Homotopy.Contractible


/-! Each radial vertex star in an arbitrary disk attachment is genuinely
contractible. The contraction fixes the old vertex and works for infinitely
many incident cells. Pending Lean verification. -/

noncomputable section

namespace FiniteChains.RelativeAttachment

variable {E V J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace V]

def vertexStar (r : BoundaryFamily J E → V) (v : V) :=
  oldCollar r 0 le_rfl {v}

omit [TopologicalSpace V] in
theorem vertexStar_subset_core (r : BoundaryFamily J E → V) (v : V) :
    vertexStar r v ⊆ puncturedAttachment r := by
  rintro (x | d) hx
  · trivial
  · exact ⟨hx.choose, trivial⟩

def vertexStarPoint (r : BoundaryFamily J E → V) v : vertexStar r v :=
  ⟨old r _ v, rfl⟩

theorem vertexStar_isOpen [DiscreteTopology V] (r : BoundaryFamily J E → V)
    (hr : Continuous r) v : IsOpen (vertexStar r v) :=
  oldCollar_isOpen r hr 0 le_rfl zero_lt_one _ (isOpen_discrete _)

/-- Restricting the actual radial homotopy gives an actual contraction,
rather than just a claim about the induced fundamental group. -/
def vertexStarContraction (r : BoundaryFamily J E → V) (hr : Continuous r) v :
    ContinuousMap.Homotopy (ContinuousMap.id (vertexStar r v))
      (ContinuousMap.const _ (vertexStarPoint r v)) := by
  let j : C(vertexStar r v, puncturedAttachment r) :=
    ⟨fun z => ⟨z.val, vertexStar_subset_core r v z.property⟩,
      continuous_subtype_val.subtype_mk _⟩
  let H := radialCoreHomotopy r hr
  refine {
    toFun := fun tx => ⟨H (tx.1, j tx.2),
      radialCoreHomotopy_mem_oldCollar r hr tx.1 _ _ tx.2.property⟩
    continuous_toFun :=
      (H.continuous.comp (continuous_fst.prodMk (j.continuous.comp continuous_snd))).subtype_mk _
    map_zero_left := ?_
    map_one_left := ?_ }
  · aesop
  · intro z
    apply Subtype.ext
    change H (1, j z) = old r _ v
    have hz :=
      (radialCoreBack_mem_iff r (j z) _).mpr z.property
    simp_all

theorem vertexStar_contractible (r : BoundaryFamily J E → V) (hr : Continuous r) v :
    ContractibleSpace (vertexStar r v) :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨vertexStarPoint r v, ⟨vertexStarContraction r hr v⟩⟩

theorem vertexStar_simplyConnected (r : BoundaryFamily J E → V) (hr : Continuous r) v :
    IsSimplyConnected (vertexStar r v) := by
  letI := vertexStar_contractible r hr v
  change SimplyConnectedSpace (vertexStar r v)
  infer_instance
