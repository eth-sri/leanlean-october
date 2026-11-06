import Mathlib.Tactic

import RequestProject.HomeomorphContinuousMap
import RequestProject.ClassicalGraphModel
import RequestProject.PathTailContraction
import RequestProject.AttachmentBaseChange

/-! Cellwise contraction of an arbitrary disk graph from compatible vertex
paths. Compactness is used only for the homotopy time parameter. -/

noncomputable section
namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped unitInterval Topology Classical

variable {V J : Type} [TopologicalSpace V]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V) (root : V)


variable (Q : ∀ a : V, Path ((old r (boundaryFamilyInclusion J (Fin 1 → ℝ))) a) ((old r (boundaryFamilyInclusion J (Fin 1 → ℝ))) root))
  (hQ : ∀ j : J,
    Q (graphSrc r j) = (graphEdgePath r j).trans (Q (graphTgt r j)) ∨
    Q (graphTgt r j) = (graphEdgePath r j).symm.trans (Q (graphSrc r j)))

variable (j : J)
include hQ in
theorem graphEdgeContraction_exists  : ∃ H : C(I × I, (DiskAttachment r)),
    (∀ s, H (0, s) = graphEdgePath r j s) ∧
    (∀ s, H (1, s) = (old r (boundaryFamilyInclusion J (Fin 1 → ℝ))) root) ∧
    (∀ t, H (t, 0) = Q (graphSrc r j) t) ∧
    (∀ t, H (t, 1) = Q (graphTgt r j) t) := by
  rcases hQ j with hj | hj
  · let H := (Path.tailContraction (graphEdgePath r j).symm (Q (graphTgt r j))).comp
      ⟨fun ts : I × I => (ts.1, unitInterval.symm ts.2),
        continuous_fst.prodMk (unitInterval.continuous_symm.comp continuous_snd)⟩
    refine ⟨H, ?_, ?_, ?_, ?_⟩
    · aesop
    · intro s
      exact Path.tailContraction_one _ _ _
    · aesop
    aesop
  · refine ⟨Path.tailContraction (graphEdgePath r j) (Q (graphSrc r j)),
      Path.tailContraction_zero _ _, Path.tailContraction_one _ _,
      Path.tailContraction_left _ _, ?_⟩
    intro t
    rw [Path.tailContraction_right, ← hj]

def graphEdgeContraction   :=
  Classical.choose (graphEdgeContraction_exists r root Q hQ j)

theorem graphEdgeContraction_spec  :
    (∀ s, graphEdgeContraction r root Q hQ j (0, s) = graphEdgePath r j s) ∧
    (∀ s, graphEdgeContraction r root Q hQ j (1, s) = (old r (boundaryFamilyInclusion J (Fin 1 → ℝ))) root) ∧
    (∀ t, graphEdgeContraction r root Q hQ j (t, 0) = Q (graphSrc r j) t) ∧
    (∀ t, graphEdgeContraction r root Q hQ j (t, 1) = Q (graphTgt r j) t) :=
  Classical.choose_spec (graphEdgeContraction_exists r root Q hQ j)

variable [DiscreteTopology V]

def graphVertexContraction  :=
  (⟨fun a => (Q a).toContinuousMap, continuous_of_discreteTopology⟩ : C(V, C(I, (DiskAttachment r)))).uncurry.comp
    ⟨Prod.swap, continuous_swap⟩

def graphDiskContraction  : C(I × ClosedUnitBall (Fin 1 → ℝ), (DiskAttachment r)) :=
  (graphEdgeContraction r root Q hQ j).comp
    ⟨fun td => (td.1, graphDiskHomeomorph.symm td.2),
      continuous_fst.prodMk (graphDiskHomeomorph.symm.continuous.comp continuous_snd)⟩

def graphDiskFamilyContraction  :=
  let F : C(DiskFamily J (Fin 1 → ℝ), C(I, (DiskAttachment r))) := {
    toFun := fun d => ((graphDiskContraction r root Q hQ d.1).comp
      ⟨Prod.swap, continuous_swap⟩).curry d.2
    continuous_toFun := continuous_sigma (fun j =>
      ((graphDiskContraction r root Q hQ j).comp ⟨Prod.swap, continuous_swap⟩).curry.continuous) }
  F.uncurry.comp ⟨Prod.swap, continuous_swap⟩

theorem graphContraction_compatible (t : I) (a : BoundaryFamily J (Fin 1 → ℝ)) :
    graphVertexContraction r root Q (t, r a) =
      graphDiskFamilyContraction r root Q hQ (t, boundaryFamilyInclusion J _ a) := by
  rcases a with ⟨j, a⟩
  rcases graphBoundary_cases a with rfl | rfl
  · change Q (graphSrc r j) t =
      graphEdgeContraction r root Q hQ j
        (t, graphDiskHomeomorph.symm (unitBoundaryInclusion _ graphBoundaryNeg))
    simp_all [graphEdgeContraction_spec]
  · change Q (graphTgt r j) t =
      graphEdgeContraction r root Q hQ j
        (t, graphDiskHomeomorph.symm (unitBoundaryInclusion _ graphBoundaryPos))
    simp_all [graphEdgeContraction_spec]

/-- Compatible vertex paths and edge recursions contract the actual quotient
topology of the graph. Neither the vertex set nor the edge set is finite. -/
def graphContraction : ContinuousMap.Homotopy (ContinuousMap.id (DiskAttachment r))
    (ContinuousMap.const (DiskAttachment r) ((old r (boundaryFamilyInclusion J (Fin 1 → ℝ))) root)) where
  toContinuousMap := attachmentHomotopyPasting r (boundaryFamilyInclusion J _)
    (graphVertexContraction r root Q) (graphDiskFamilyContraction r root Q hQ)
    (graphContraction_compatible r root Q hQ)
  map_zero_left z := by
    obtain ⟨w, rfl⟩ := quotientMap_surjective r (boundaryFamilyInclusion J _) z
    cases w with
    | inl a => exact (Q a).source
    | inr d =>
        change attachmentHomotopyPasting r (boundaryFamilyInclusion J (Fin 1 → ℝ))
          (graphVertexContraction r root Q) (graphDiskFamilyContraction r root Q hQ)
          (graphContraction_compatible r root Q hQ)
          (0, cell r (boundaryFamilyInclusion J (Fin 1 → ℝ)) d) = _
        rw [attachmentHomotopyPasting_cell]
        change graphEdgeContraction r root Q hQ d.1 (0, graphDiskHomeomorph.symm d.2) = _
        rw [(graphEdgeContraction_spec r root Q hQ d.1).1]
        
        exact congrArg (fun x : ClosedUnitBall (Fin 1 → ℝ) =>
          cell r (boundaryFamilyInclusion J (Fin 1 → ℝ)) ⟨d.1, x⟩)
          (graphDiskHomeomorph.apply_symm_apply d.2)
  map_one_left z := by
    obtain ⟨w, rfl⟩ := quotientMap_surjective r (boundaryFamilyInclusion J _) z
    cases w with
    | inl a => exact (Q a).target
    | inr d =>
        change attachmentHomotopyPasting r (boundaryFamilyInclusion J (Fin 1 → ℝ))
          (graphVertexContraction r root Q) (graphDiskFamilyContraction r root Q hQ)
          (graphContraction_compatible r root Q hQ)
          (1, cell r (boundaryFamilyInclusion J (Fin 1 → ℝ)) d) = _
        rw [attachmentHomotopyPasting_cell]
        exact (graphEdgeContraction_spec r root Q hQ d.1).2.1 _



end FiniteChains.ClassicalGraphModel
