import Mathlib.Tactic

import RequestProject.HomeomorphContinuousMap
import RequestProject.ClassicalRoseWordReduction
import RequestProject.BoundaryWordsLoopMatching
import RequestProject.DiskRoseMaps
import RequestProject.DummyLoopFilling
import RequestProject.FinitePosetCycleNaturality

/-! Actual word-reading naturality and the boundary of the added filled
circle. All statements concern the continuous attaching maps themselves.
Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb RelativeAttachment ClassicalGraphModel ContinuousEdgeWords

variable {A B : Type}

theorem classicalRoseRead_map (f : A → B) (l : List (A × Bool)) (t : I) :
    diskRoseMap f (classicalRoseRead l t) =
      classicalRoseRead (l.map (fun p => (f p.1, p.2))) t := by
  induction l generalizing t with
  | nil => exact diskRoseMap_vertex f
  | cons p l ih =>
    rcases p with ⟨a, b⟩
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · simp only [List.map_cons, classicalRoseRead, Path.trans_apply, dif_pos ht]
      cases b <;> simp 
      all_goals exact diskRoseMap_cell f _
    · simp only [List.map_cons, classicalRoseRead, Path.trans_apply, dif_neg ht]
      exact ih _

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
      (graphEdgePath (roseAttaching A)) l hl t := by
  solve_by_elim [FiniteChains.PresModel.classicalRoseRead_eq_realize]

theorem boundaryWords_homotopic_classicalWord (W : BoundaryWords (roseAttaching A)) :
    W.boundaryMap.Homotopic (classicalRoseWordBoundary W.loopWord) := by
  classical grind [FiniteChains.ClassicalGraphModel.BoundaryWords.loopWord_isPath, FiniteChains.ClassicalGraphModel.BoundaryWords.boundaryMap_homotopic_word, FiniteChains.RelativeAttachment.squareBoundaryTraversal_surjective, FiniteChains.PresModel.classicalRoseRead_eq_realize_apply, squareLoopDesc, realize, graphSrc, roseAttaching, graphTgt, old, boundaryFamilyInclusion, graphEdgePath, classicalRoseWordBoundary]

theorem roseCopyRealization_unit (x : orderNerveRealization (Rose PUnit)) :
    roseCopyRealization PUnit.unit x = x := by
  
  have hf : (roseCopy PUnit.unit : Rose PUnit → Rose PUnit) = id := by
    funext p
    cases p with
    | base => rfl
    | mid u => cases u; rfl
    | edg u b => cases u; rfl
  have mapEq (g : Rose PUnit → Rose PUnit) (hg : Monotone g) (he : g = id) :
      orderNerveRealizationMap g hg x = x := by
    subst g
    exact orderNerveRealizationMap_id _ _
  exact mapEq (roseCopy PUnit.unit) (roseCopy PUnit.unit).monotone hf

theorem dummyCircleBoundaryHomeomorph_traversal (t : I) :
    dummyCircleBoundaryHomeomorph
      (unitBoundarySquareHomeomorph.symm (squareBoundaryTraversal t)) =
        graphEdgePath (roseAttaching PUnit) PUnit.unit t := by
  dsimp [FiniteChains.ClassicalGraphModel.dummyCircleBoundaryHomeomorph]
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
  dsimp
  rw [Homeomorph.apply_symm_apply, squareLoopDesc_traversal]
  exact dummyCircleBoundaryHomeomorph_traversal t

theorem dummyCircleBoundaryHomeomorph_homotopic_word :
    dummyCircleBoundaryHomeomorph.toContinuousMap.Homotopic
      (classicalRoseWordBoundary [(PUnit.unit, true)]) := by
  have H := (squareLoopDesc_homotopic
    (Path.Homotopic.trans_refl (graphEdgePath (roseAttaching PUnit) PUnit.unit)).symm).comp
      (ContinuousMap.Homotopic.refl unitBoundarySquareHomeomorph.toContinuousMap)
  rw [← dummyCircleBoundaryHomeomorph_eq] at H
  exact H

end FiniteChains.PresModel
