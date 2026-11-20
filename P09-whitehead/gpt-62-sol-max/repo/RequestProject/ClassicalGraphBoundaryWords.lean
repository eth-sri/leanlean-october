module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.ClassicalGraphPathStraightening
public import RequestProject.IntervalEndpointHomotopyExtension
public import RequestProject.SquareBoundaryNormHomeomorph

@[expose] public section

/-! Genuine attaching-circle maps into a graph can be replaced by finite
words in its actual edges, through homotopies entirely in that graph. Four
side words retain their exact parametrized attaching map. Pending Lean
verification. -/

noncomputable section
open scoped Classical unitInterval
open Set Topology

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment ContinuousEdgeWords

variable {V J : Type} [TopologicalSpace V]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V)

/-- Finite words on the four sides, with their exact corner incidences. -/
structure BoundaryWords where
  vertex : SquareBoundary → V
  word : SquareSide → List (J × Bool)
  isPath : ∀ s, Comb.IsPath (graphSrc r) (graphTgt r) (word s)
    (vertex (squareSideMap s 0)) (vertex (squareSideMap s 1))

namespace BoundaryWords

variable {r} (W : BoundaryWords r)

def sidePath (s : SquareSide) :
    Path (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (W.vertex (squareSideMap s 0)))
      (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (W.vertex (squareSideMap s 1))) :=
  realize (graphSrc r) (graphTgt r) (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)))
    (graphEdgePath r) (W.word s) (W.isPath s)

theorem sidePath_endpoint (s : SquareSide) (t : I) (ht : t = 0 ∨ t = 1) :
    W.sidePath s t = old r (boundaryFamilyInclusion J (Fin 1 → ℝ))
      (W.vertex (squareSideMap s t)) := by
  aesop

def squareMap : C(SquareBoundary, DiskAttachment r) :=
  boundaryOfPaths (v := fun z => old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (W.vertex z)) W.sidePath

@[simp] theorem squareMap_side (s : SquareSide) (t : I) :
    W.squareMap (squareSideMap s t) = W.sidePath s t :=
  boundaryOfPaths_side _ _ _

def boundaryMap : C(UnitBoundary (Fin 2 → ℝ), DiskAttachment r) :=
  W.squareMap.comp unitBoundarySquareHomeomorph.toContinuousMap

/-- The based combinatorial word obtained by travelling around the four
sides, reversing the two sides whose coordinate direction opposes travel. -/
def loopWord : List (J × Bool) :=
  List.append (α := J × Bool)
    (List.append (α := J × Bool)
      (List.append (W.word (0, false)) (W.word (1, true)))
      (Comb.revPath (X := graphCx r) (W.word (0, true))))
    (Comb.revPath (X := graphCx r) (W.word (1, false)))

theorem corner01 : squareSideMap (0, false) 1 = squareSideMap (1, true) 0 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

theorem corner11 : squareSideMap (1, true) 1 = squareSideMap (0, true) 1 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

theorem corner10 : squareSideMap (0, true) 0 = squareSideMap (1, false) 1 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

theorem corner00 : squareSideMap (1, false) 0 = squareSideMap (0, false) 0 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

omit [TopologicalSpace V] in
theorem loopWord_isPath : Comb.IsPath (graphSrc r) (graphTgt r) W.loopWord
    (W.vertex (squareSideMap (0, false) 0)) (W.vertex (squareSideMap (0, false) 0)) := by
  have h₀ := W.isPath (0, false)
  have h₁ := W.isPath (1, true)
  have h₂ := Comb.isPath_revPath (X := graphCx r) (W.isPath (0, true))
  have h₃ := Comb.isPath_revPath (X := graphCx r) (W.isPath (1, false))
  rw [← corner01] at h₁
  rw [← corner11] at h₂
  rw [← corner10, corner00] at h₃
  exact ((h₀.append h₁).append h₂).append h₃

end BoundaryWords

/-- The endpoint motions and edge-word homotopies descend through the
actual four-side quotient. No cellular approximation premise is assumed. -/
theorem squareMap_homotopic_boundaryWords [DiscreteTopology V] (hr : Continuous r)
    (f : C(SquareBoundary, DiskAttachment r)) :
    ∃ W : BoundaryWords r, f.Homotopic W.squareMap := by
  let v z := graphSnap r (f z)
  obtain ⟨l, hl⟩ := homotopic_boundaryOfPaths f _ (fun z => graphConnector r (f z))
  choose w hw hp using fun s => graph_path_isWord r hr _ _ (l s)
  exact ⟨⟨v, w, hw⟩, hl.trans (boundaryOfPaths_homotopic hp)⟩

theorem boundaryMap_homotopic_boundaryWords [DiscreteTopology V] (hr : Continuous r)
    (f : C(UnitBoundary (Fin 2 → ℝ), DiskAttachment r)) :
    ∃ W : BoundaryWords r, f.Homotopic W.boundaryMap := by
  let e := unitBoundarySquareHomeomorph
  obtain ⟨W, hW⟩ := squareMap_homotopic_boundaryWords r hr (f.comp e.symm.toContinuousMap)
  refine ⟨W, ?_⟩
  have H := hW.comp (ContinuousMap.Homotopic.refl e.toContinuousMap)
  aesop

end FiniteChains.ClassicalGraphModel
