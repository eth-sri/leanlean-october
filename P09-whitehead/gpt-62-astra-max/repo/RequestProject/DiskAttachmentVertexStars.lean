module

public import RequestProject.DiskAttachmentRadialCore
public import Mathlib.Topology.Homotopy.Contractible

@[expose] public section

/-! Each radial vertex star in an arbitrary disk attachment is genuinely
contractible. The contraction fixes the old vertex and works for infinitely
many incident cells. Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval
open Set Topology

namespace FiniteChains.RelativeAttachment

variable {E V J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace V]

variable (r : BoundaryFamily J E → V) (v : V)

def vertexStar :=
  oldCollar r 0 le_rfl {v}

omit [TopologicalSpace V] in
theorem vertexStar_subset_core :
    vertexStar r v ⊆ puncturedAttachment r := by
  rintro (x | d) hx
  · trivial
  · exact ⟨hx.choose, trivial⟩

def vertexStarPoint : vertexStar r v :=
  ⟨old r _ v, rfl⟩

theorem vertexStar_isOpen [DiscreteTopology V] (r : BoundaryFamily J E → V)
    (hr : Continuous r) (v : V) : IsOpen (vertexStar r v) :=
  oldCollar_isOpen r hr 0 le_rfl zero_lt_one _ (isOpen_discrete _)

variable (r : BoundaryFamily J E → V) (hr : Continuous r) (v : V)
include hr

/-- Restricting the actual radial homotopy gives an actual contraction,
rather than just a claim about the induced fundamental group. -/
def vertexStarContraction :
    ContinuousMap.Homotopy (ContinuousMap.id _)
      (ContinuousMap.const _ (vertexStarPoint r v)) := by
  let j : C(vertexStar r v, puncturedAttachment r) :=
    ⟨fun z => ⟨z.val, vertexStar_subset_core r v z.property⟩,
      continuous_subtype_val.subtype_mk _⟩
  let H := radialCoreHomotopy r hr
  refine {
    toFun := fun tx => ⟨H _,
      radialCoreHomotopy_mem_oldCollar r hr tx.1 (j tx.2) _ tx.2.property⟩
    continuous_toFun :=
      (H.continuous.comp (continuous_fst.prodMk (j.continuous.comp continuous_snd))).subtype_mk _
    map_zero_left := ?_
    map_one_left := ?_ }
  · aesop
  · intro z
    apply Subtype.ext
    refine (H.map_one_left _).trans ?_; exact congrArg _ ((radialCoreBack_mem_iff r (j z) {v}).mpr z.property)

theorem vertexStar_contractible :
    ContractibleSpace (vertexStar r v) :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨vertexStarPoint r v, ⟨vertexStarContraction r hr v⟩⟩

theorem vertexStar_simplyConnected :
    IsSimplyConnected (vertexStar r v) := by
  letI := vertexStar_contractible r hr v
  change SimplyConnectedSpace (vertexStar r v)
  infer_instance

end FiniteChains.RelativeAttachment
