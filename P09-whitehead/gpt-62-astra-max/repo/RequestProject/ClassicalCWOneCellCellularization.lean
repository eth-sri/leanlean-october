module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.ClassicalCWVertexPaths
public import RequestProject.ClassicalCellAttachmentCW

@[expose] public section

/-! Cellularization of the endpoints of any family of new one-cells in the
literal original CW complex. Each endpoint is moved along an actual path to
an original vertex, with an explicit simultaneous attaching homotopy and finite
zero-cell support. Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval
open Set Topology

namespace FiniteChains.RelativeAttachment

theorem oneBoundary_finiteSet :
    ({x : Fin 1 → ℝ | ‖x‖ = 1}).Finite := by
  apply ((Set.finite_singleton (fun _ : Fin 1 => (-1))).insert
    (fun _ : Fin 1 => 1)).subset
  intro x hx
  have he : x = fun _ : Fin 1 => x 0 := by
    funext i
    exact congrArg x (Subsingleton.elim i 0)
  have hx' : |x 0| = 1 := by
    calc
      |x 0| = ‖fun _ : Fin 1 => x 0‖ := by simp
      _ = ‖x‖ := congrArg norm he.symm
      _ = 1 := hx
  grind

instance oneBoundary_finite : Finite (UnitBoundary (Fin 1 → ℝ)) :=
  oneBoundary_finiteSet.to_subtype

instance oneBoundary_discrete : DiscreteTopology (UnitBoundary (Fin 1 → ℝ)) := inferInstance

variable {X J : Type} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]

/-- The new one-cell endpoints are chosen among original zero-cells. -/
def vertexBoundaryMap (r : BoundaryFamily J (Fin 1 → ℝ) → X) :
    C(BoundaryFamily J (Fin 1 → ℝ), X) :=
  ⟨fun a => ClassicalCW.vertexPoint (ClassicalCW.pointVertex (r a)), continuous_of_discreteTopology⟩

/-- Arbitrarily many endpoints move simultaneously. Their disjoint domain
is discrete, so the chosen vertex paths give a continuous homotopy. -/
def vertexBoundaryHomotopy (r : C(BoundaryFamily J (Fin 1 → ℝ), X)) :
    ContinuousMap.Homotopy r (vertexBoundaryMap r) := by
  let F : C(BoundaryFamily J (Fin 1 → ℝ), C(I, X)) :=
    ⟨fun a => (ClassicalCW.pointVertexPath (r a)).toContinuousMap,
      continuous_of_discreteTopology⟩
  exact {
    toContinuousMap := F.uncurry.comp ⟨Prod.swap, continuous_swap⟩
    map_zero_left := fun a => (ClassicalCW.pointVertexPath (r a)).source
    map_one_left := fun a => (ClassicalCW.pointVertexPath (r a)).target }

theorem vertexBoundaryMap_finiteLowerBoundary
    (r : BoundaryFamily J (Fin 1 → ℝ) → X) :
    FiniteLowerBoundary 1 (vertexBoundaryMap r) := by
  classical
  letI := Fintype.ofFinite (UnitBoundary (Fin 1 → ℝ))
  intro j
  let cells : ∀ m, Finset _
    | 0 => Finset.univ.image (fun a : UnitBoundary (Fin 1 → ℝ) => ClassicalCW.pointVertex (r ⟨j, a⟩))
    | _ + 1 => ∅
  refine ⟨cells, ?_⟩
  intro a
  simp only [Set.mem_iUnion]
  refine ⟨0, Nat.zero_lt_one, ClassicalCW.pointVertex (r ⟨j, a⟩), ?_, ?_⟩
  · grind
  · rw [RelCWComplex.closedCell_zero_eq_singleton]
    rfl

end FiniteChains.RelativeAttachment
