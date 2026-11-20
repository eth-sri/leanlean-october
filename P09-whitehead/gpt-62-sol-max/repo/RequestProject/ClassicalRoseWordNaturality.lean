module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.ClassicalRoseWordReduction
public import RequestProject.BoundaryWordsLoopMatching
public import RequestProject.DiskRoseMaps
public import RequestProject.DummyLoopFilling
public import RequestProject.FinitePosetCycleNaturality

@[expose] public section

/-! Actual word-reading naturality and the boundary of the added filled
circle. All statements concern the continuous attaching maps themselves.
Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval Topology
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.PresModel
open Comb RelativeAttachment ClassicalGraphModel ContinuousEdgeWords

variable {A B : Type}

theorem classicalRoseRead_map (f : A → B) (l : List (A × Bool)) (t : I) :
    diskRoseMap f (classicalRoseRead l t) =
      classicalRoseRead (l.map (fun p => (f p.1, p.2))) t := by
  exact readLoopWord_map (diskRoseMap f) f
    (fun a => (graphEdgePath (roseAttaching A) a : Path (roseVertex A) (roseVertex A)))
    (fun b => (graphEdgePath (roseAttaching B) b : Path (roseVertex B) (roseVertex B)))
    (diskRoseMap_vertex f) (fun a t => diskRoseMap_cell f ⟨a, graphDiskHomeomorph t⟩) l t

theorem classicalRoseWordBoundary_map (f : A → B) (l : List (A × Bool)) :
    (diskRoseMap f).comp (classicalRoseWordBoundary l) =
      classicalRoseWordBoundary (l.map (fun p => (f p.1, p.2))) := by
  apply ContinuousMap.ext
  intro z
  exact classicalRoseRead_map f l _

theorem classicalRoseRead_eq_realize_apply (l : List (A × Bool))
    {a b : PUnit}
    (hl : IsPath (graphSrc (roseAttaching A)) (graphTgt (roseAttaching A)) l a b) (t : I) :
    classicalRoseRead l t = realize (graphSrc (roseAttaching A)) (graphTgt (roseAttaching A))
      (old (roseAttaching A) (boundaryFamilyInclusion A (Fin 1 → ℝ)))
      (graphEdgePath (roseAttaching A)) l hl t := congrArg (fun p => p t) (classicalRoseRead_eq_realize l hl)

theorem boundaryWords_homotopic_classicalWord (W : BoundaryWords (roseAttaching A)) :
    W.boundaryMap.Homotopic (classicalRoseWordBoundary W.loopWord) := by
  have H := W.boundaryMap_homotopic_word
  have he : ((squareLoopDesc (realize (graphSrc (roseAttaching A)) (graphTgt (roseAttaching A))
      (old (roseAttaching A) (boundaryFamilyInclusion A (Fin 1 → ℝ)))
      (graphEdgePath (roseAttaching A)) W.loopWord W.loopWord_isPath)).comp
        unitBoundarySquareHomeomorph.toContinuousMap) = classicalRoseWordBoundary W.loopWord := by
    apply ContinuousMap.ext
    intro z
    exact (classicalRoseRead_eq_realize_apply W.loopWord W.loopWord_isPath _).symm
  rwa [he] at H

theorem roseCopyRealization_unit (x : orderNerveRealization (Rose PUnit)) :
    roseCopyRealization PUnit.unit x = x := by
  change orderNerveRealizationMap (roseCopy PUnit.unit) (roseCopy PUnit.unit).monotone x = x
  have hf : (roseCopy PUnit.unit : Rose PUnit → Rose PUnit) = id := by
    funext p
    cases p with
    | base => rfl
    | mid u => cases u; rfl
    | edg u b => cases u; rfl
  grind [orderNerveRealizationMap_id]

theorem dummyCircleBoundaryHomeomorph_traversal (t : I) :
    dummyCircleBoundaryHomeomorph
      (unitBoundarySquareHomeomorph.symm (squareBoundaryTraversal t)) =
        graphEdgePath (roseAttaching PUnit) PUnit.unit t := by
  change orderRoseRealizationHomeomorph PUnit
    (roseFourCycle.boundaryHomeomorph.symm
      (unitBoundarySquareHomeomorph.symm (squareBoundaryTraversal t))) = _
  rw [← roseFourCycle.boundaryHomeomorph_traversal, Homeomorph.symm_apply_apply]
  change orderRoseRealizationHomeomorph PUnit (orderRoseTraversal t) = _
  rw [← roseCopyRealization_unit (orderRoseTraversal t), orderRoseRealizationHomeomorph_interval]
  rfl

theorem dummyCircleBoundaryHomeomorph_eq :
    dummyCircleBoundaryHomeomorph.toContinuousMap =
      (squareLoopDesc (graphEdgePath (roseAttaching PUnit) PUnit.unit)).comp
        unitBoundarySquareHomeomorph.toContinuousMap := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, ht⟩ := squareBoundaryTraversal_surjective (unitBoundarySquareHomeomorph z)
  have hz : unitBoundarySquareHomeomorph.symm (squareBoundaryTraversal t) = z := by
    rw [ht, Homeomorph.symm_apply_apply]
  rw [← hz]
  change dummyCircleBoundaryHomeomorph
    (unitBoundarySquareHomeomorph.symm (squareBoundaryTraversal t)) =
      squareLoopDesc (graphEdgePath (roseAttaching PUnit) PUnit.unit)
    (unitBoundarySquareHomeomorph (unitBoundarySquareHomeomorph.symm (squareBoundaryTraversal t)))
  simpa using dummyCircleBoundaryHomeomorph_traversal t

theorem dummyCircleBoundaryHomeomorph_homotopic_word :
    dummyCircleBoundaryHomeomorph.toContinuousMap.Homotopic
      (classicalRoseWordBoundary [(PUnit.unit, true)]) := by
  have H := (squareLoopDesc_homotopic
    (Path.Homotopic.trans_refl (graphEdgePath (roseAttaching PUnit) PUnit.unit)).symm).comp
      (ContinuousMap.Homotopic.refl unitBoundarySquareHomeomorph.toContinuousMap)
  simpa [← dummyCircleBoundaryHomeomorph_eq] using! H

end FiniteChains.PresModel
