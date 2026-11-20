module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.ClassicalGraphModel
public import RequestProject.PathTailContraction
public import RequestProject.AttachmentBaseChange

@[expose] public section

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

include hQ in
theorem graphEdgeContraction_exists (j : J) : ∃ H : C(I × I, (DiskAttachment r)),
    (∀ s, H (0, s) = graphEdgePath r j s) ∧
    (∀ s, H (1, s) = (old r (boundaryFamilyInclusion J (Fin 1 → ℝ))) root) ∧
    (∀ t, H (t, 0) = Q (graphSrc r j) t) ∧
    (∀ t, H (t, 1) = Q (graphTgt r j) t) := by
  rcases hQ j with hj | hj
  · let H := (Path.tailContraction (graphEdgePath r j).symm (Q (graphTgt r j))).comp
      ⟨fun ts : I × I => (ts.1, unitInterval.symm ts.2),
        continuous_fst.prodMk (unitInterval.continuous_symm.comp continuous_snd)⟩
    refine ⟨H, ?_, ?_, ?_, ?_⟩
    · intro s
      change Path.tailContraction _ _ (0, unitInterval.symm s) = _
      simp
    · intro s
      exact Path.tailContraction_one _ _ _
    · intro t
      change Path.tailContraction _ _ (t, unitInterval.symm 0) = _
      simp [← hj]
    · intro t
      change Path.tailContraction _ _ (t, unitInterval.symm 1) = _
      rw [unitInterval.symm_one, Path.tailContraction_left]
  · refine ⟨Path.tailContraction (graphEdgePath r j) (Q (graphSrc r j)),
      Path.tailContraction_zero _ _, Path.tailContraction_one _ _,
      Path.tailContraction_left _ _, ?_⟩
    intro t
    simp [← hj]

def graphEdgeContraction (j : J) : C(I × I, (DiskAttachment r)) :=
  Classical.choose (graphEdgeContraction_exists r root Q hQ j)

theorem graphEdgeContraction_spec (j : J) :
    (∀ s, graphEdgeContraction r root Q hQ j (0, s) = graphEdgePath r j s) ∧
    (∀ s, graphEdgeContraction r root Q hQ j (1, s) = (old r (boundaryFamilyInclusion J (Fin 1 → ℝ))) root) ∧
    (∀ t, graphEdgeContraction r root Q hQ j (t, 0) = Q (graphSrc r j) t) ∧
    (∀ t, graphEdgeContraction r root Q hQ j (t, 1) = Q (graphTgt r j) t) :=
  Classical.choose_spec (graphEdgeContraction_exists r root Q hQ j)

variable [DiscreteTopology V]

def graphVertexContraction : C(I × V, (DiskAttachment r)) :=
  (⟨fun a => (Q a).toContinuousMap, continuous_of_discreteTopology⟩ : C(V, C(I, (DiskAttachment r)))).uncurry.comp
    .prodSwap

def graphDiskContraction (j : J) : C(I × ClosedUnitBall (Fin 1 → ℝ), (DiskAttachment r)) :=
  (graphEdgeContraction r root Q hQ j).comp
    (ContinuousMap.prodMap (.id I) graphDiskHomeomorph.symm.toContinuousMap)

def graphDiskFamilyContraction : C(I × DiskFamily J (Fin 1 → ℝ), (DiskAttachment r)) :=
  (ContinuousMap.sigma fun j => ((graphDiskContraction r root Q hQ j).comp .prodSwap).curry
    ).uncurry.comp .prodSwap

theorem graphContraction_compatible (t : I) (a : BoundaryFamily J (Fin 1 → ℝ)) :
    graphVertexContraction r root Q (t, r a) =
      graphDiskFamilyContraction r root Q hQ (t, boundaryFamilyInclusion J _ a) := by
  rcases a with ⟨j, a⟩
  rcases graphBoundary_cases a with rfl | rfl
  · change Q (graphSrc r j) t =
      graphEdgeContraction r root Q hQ j
        (t, graphDiskHomeomorph.symm (unitBoundaryInclusion _ graphBoundaryNeg))
    simpa using ((graphEdgeContraction_spec r root Q hQ j).2.2.1 t).symm
  · change Q (graphTgt r j) t =
      graphEdgeContraction r root Q hQ j
        (t, graphDiskHomeomorph.symm (unitBoundaryInclusion _ graphBoundaryPos))
    simpa using ((graphEdgeContraction_spec r root Q hQ j).2.2.2 t).symm

/-- Compatible vertex paths and edge recursions contract the actual quotient
topology of the graph. Neither the vertex set nor the edge set is finite. -/
def graphContraction : ContinuousMap.Homotopy (ContinuousMap.id (DiskAttachment r))
    (ContinuousMap.const (DiskAttachment r) ((old r (boundaryFamilyInclusion J (Fin 1 → ℝ))) root)) := by
  refine attachmentHomotopy r (boundaryFamilyInclusion J _)
    (graphVertexContraction r root Q) (graphDiskFamilyContraction r root Q hQ)
    (graphContraction_compatible r root Q hQ)
    ⟨fun a => (Q a).source, ?_⟩ ⟨fun a => (Q a).target, ?_⟩
  · intro d
    change graphEdgeContraction r root Q hQ d.1 (0, graphDiskHomeomorph.symm d.2) = _
    rw [(graphEdgeContraction_spec r root Q hQ d.1).1]
    change cell r (boundaryFamilyInclusion J (Fin 1 → ℝ))
      ⟨d.1, graphDiskHomeomorph (graphDiskHomeomorph.symm d.2)⟩ = _
    rw [graphDiskHomeomorph.apply_symm_apply]
    rfl
  · exact fun d => (graphEdgeContraction_spec r root Q hQ d.1).2.1 _


end FiniteChains.ClassicalGraphModel
