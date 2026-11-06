import Mathlib.Tactic

import RequestProject.VertexPunctureIntersection
import RequestProject.NerveThreeLegContraction
import RequestProject.NerveSupport

/-! An explicit contraction of the actual seven-cell intersection path. -/
namespace FiniteChains.Davis
open Comb Nerve

abbrev VertexIntersection :=
  {c : VertexPuncturedCube // vertexPunctureLeft c ∧ vertexPunctureRight c}

variable (i : Fin 7)
def vertexIntersectionPoint  : VertexIntersection :=
  ⟨vertexIntersectionCell i, vertexIntersectionCell_mem i⟩

theorem vertexIntersectionPoint_injective : Function.Injective vertexIntersectionPoint := by
  have hi : Function.Injective vertexIntersectionCoordinates := by decide
  intro i j h
  exact hi (congrArg (fun c : VertexIntersection => c.1.1) h)

theorem vertexIntersectionPoint_surjective : Function.Surjective vertexIntersectionPoint := by
  intro c
  obtain ⟨i, hi⟩ := vertexIntersection_classify c.1 c.2
  exact ⟨i, Subtype.ext hi.symm⟩

variable (c : VertexIntersection)
noncomputable def vertexIntersectionIndex   :=
  Classical.choose (vertexIntersectionPoint_surjective c)

abbrev vertexIntersectionPoint_index   :=
  Classical.choose_spec (FiniteChains.Davis.vertexIntersectionPoint_surjective c)

@[simp] theorem vertexIntersectionIndex_point  :
    vertexIntersectionIndex (vertexIntersectionPoint i) = i :=
  vertexIntersectionPoint_injective (vertexIntersectionPoint_index (vertexIntersectionPoint i))

def vertexIntersectionLowerIndex : Fin 7 → Fin 7 := ![0, 1, 2, 3, 4, 3, 2]
def vertexIntersectionUpperIndex : Fin 7 → Fin 7 := ![0, 1, 1, 4, 4, 4, 1]

noncomputable def vertexIntersectionLower   :=
  vertexIntersectionPoint (vertexIntersectionLowerIndex (vertexIntersectionIndex c))

noncomputable def vertexIntersectionUpper   :=
  vertexIntersectionPoint (vertexIntersectionUpperIndex (vertexIntersectionIndex c))

@[simp] theorem vertexIntersectionLower_point  :
    vertexIntersectionLower (vertexIntersectionPoint i) =
      vertexIntersectionPoint (vertexIntersectionLowerIndex i) := by
  simp [vertexIntersectionLower]

@[simp] theorem vertexIntersectionUpper_point  :
    vertexIntersectionUpper (vertexIntersectionPoint i) =
      vertexIntersectionPoint (vertexIntersectionUpperIndex i) := by
  simp [vertexIntersectionUpper]

theorem vertexIntersectionLower_monotone : Monotone vertexIntersectionLower := by
  have h : ∀ i j : Fin 7,
      CoordinateFace (vertexIntersectionCoordinates i) (vertexIntersectionCoordinates j) →
      CoordinateFace (vertexIntersectionCoordinates (vertexIntersectionLowerIndex i))
        (vertexIntersectionCoordinates (vertexIntersectionLowerIndex j)) := by unfold CoordinateFace; decide
  intro c d hcd
  obtain ⟨i, rfl⟩ := vertexIntersectionPoint_surjective c
  obtain ⟨j, rfl⟩ := vertexIntersectionPoint_surjective d
  rw [vertexIntersectionLower_point, vertexIntersectionLower_point]
  exact h i j hcd

theorem vertexIntersectionUpper_monotone : Monotone vertexIntersectionUpper := by
  have h : ∀ i j : Fin 7,
      CoordinateFace (vertexIntersectionCoordinates i) (vertexIntersectionCoordinates j) →
      CoordinateFace (vertexIntersectionCoordinates (vertexIntersectionUpperIndex i))
        (vertexIntersectionCoordinates (vertexIntersectionUpperIndex j)) := by unfold CoordinateFace; decide
  intro c d hcd
  obtain ⟨i, rfl⟩ := vertexIntersectionPoint_surjective c
  obtain ⟨j, rfl⟩ := vertexIntersectionPoint_surjective d
  rw [vertexIntersectionUpper_point, vertexIntersectionUpper_point]
  exact h i j hcd

theorem vertexIntersectionLower_le  : vertexIntersectionLower c ≤ c := by
  have h : ∀ i : Fin 7, CoordinateFace
      (vertexIntersectionCoordinates (vertexIntersectionLowerIndex i))
      (vertexIntersectionCoordinates i) := by unfold CoordinateFace; decide
  obtain ⟨i, rfl⟩ := vertexIntersectionPoint_surjective c
  rw [vertexIntersectionLower_point]
  exact h i

theorem vertexIntersectionLower_le_upper  :
    vertexIntersectionLower c ≤ vertexIntersectionUpper c := by
  have h : ∀ i : Fin 7, CoordinateFace
      (vertexIntersectionCoordinates (vertexIntersectionLowerIndex i))
      (vertexIntersectionCoordinates (vertexIntersectionUpperIndex i)) := by unfold CoordinateFace; decide
  obtain ⟨i, rfl⟩ := vertexIntersectionPoint_surjective c
  rw [vertexIntersectionLower_point, vertexIntersectionUpper_point]
  exact h i

theorem vertexIntersectionPoint_zero_le_upper  :
    vertexIntersectionPoint 0 ≤ vertexIntersectionUpper c := by
  have h : ∀ i : Fin 7, CoordinateFace (vertexIntersectionCoordinates 0)
      (vertexIntersectionCoordinates (vertexIntersectionUpperIndex i)) := by unfold CoordinateFace; decide
  obtain ⟨i, rfl⟩ := vertexIntersectionPoint_surjective c
  rw [vertexIntersectionUpper_point]
  exact h i

/-- The actual intersection is acyclic in all augmented nerve degrees. -/
theorem vertexPuncture_intersection_acyclic :
    AcyclicIn (fun c : VertexPuncturedCube => vertexPunctureLeft c ∧ vertexPunctureRight c) := by
  apply acyclicIn_of_subtype _ ⟨vertexIntersectionCell 0, vertexIntersectionCell_mem 0⟩
  intro c hc hcyc
  exact exists_bdry_eq_of_cycle_threeLeg vertexIntersectionLower vertexIntersectionUpper
    (vertexIntersectionPoint 0) vertexIntersectionLower_monotone vertexIntersectionUpper_monotone
    vertexIntersectionLower_le vertexIntersectionLower_le_upper
    vertexIntersectionPoint_zero_le_upper c hc hcyc

end FiniteChains.Davis
