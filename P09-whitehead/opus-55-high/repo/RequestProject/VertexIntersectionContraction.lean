import RequestProject.VertexPunctureIntersection
import RequestProject.NerveThreeLegContraction
import RequestProject.NerveSupport
noncomputable section


/-! An explicit contraction of the actual seven-cell intersection path. -/
namespace FiniteChains.Davis
open Nerve

abbrev VertexIntersection :=
  {c : VertexPuncturedCube // vertexPunctureLeft c ∧ vertexPunctureRight c}

def vertexIntersectionPoint (i : Fin 7) : VertexIntersection :=
  ⟨vertexIntersectionCell i, vertexIntersectionCell_mem i⟩

theorem vertexIntersectionPoint_injective : Function.Injective vertexIntersectionPoint := by
  have hi : Function.Injective vertexIntersectionCoordinates := by decide
  intro i j h
  exact hi (congrArg (·.1.1) h)

theorem vertexIntersectionPoint_surjective : Function.Surjective vertexIntersectionPoint := by
  intro c
  cases' vertexIntersection_classify c.1 c.2 with i hi
  aesop

def vertexIntersectionIndex (c : VertexIntersection) :=
  Classical.choose (vertexIntersectionPoint_surjective c)

theorem vertexIntersectionPoint_index c :
    vertexIntersectionPoint (vertexIntersectionIndex c) = c :=
  Classical.choose_spec (vertexIntersectionPoint_surjective c)

@[simp] theorem vertexIntersectionIndex_point i :
    vertexIntersectionIndex (vertexIntersectionPoint i) = i :=
  vertexIntersectionPoint_injective (vertexIntersectionPoint_index _)

def vertexIntersectionLowerIndex : Fin 7 → Fin 7 := ![0, 1, 2, 3, 4, 3, 2]
def vertexIntersectionUpperIndex : Fin 7 → Fin 7 := ![0, 1, 1, 4, 4, 4, 1]

def vertexIntersectionLower (c : VertexIntersection) :=
  vertexIntersectionPoint (vertexIntersectionLowerIndex (vertexIntersectionIndex c))

def vertexIntersectionUpper (c : VertexIntersection) :=
  vertexIntersectionPoint (vertexIntersectionUpperIndex (vertexIntersectionIndex c))

@[simp] theorem vertexIntersectionLower_point i :
    vertexIntersectionLower (vertexIntersectionPoint i) =
      vertexIntersectionPoint (vertexIntersectionLowerIndex i) := by
  simp [vertexIntersectionLower]

@[simp] theorem vertexIntersectionUpper_point i :
    vertexIntersectionUpper (vertexIntersectionPoint i) =
      vertexIntersectionPoint (vertexIntersectionUpperIndex i) := by
  simp [vertexIntersectionUpper]

theorem vertexIntersectionLower_monotone : Monotone vertexIntersectionLower := by
  have h : ∀ i j,
      CoordinateFace (vertexIntersectionCoordinates i) (vertexIntersectionCoordinates j) →
      CoordinateFace (vertexIntersectionCoordinates (vertexIntersectionLowerIndex i))
        (vertexIntersectionCoordinates (vertexIntersectionLowerIndex j)) := by unfold CoordinateFace; decide
  intro c d hcd
  obtain ⟨i, rfl⟩ := vertexIntersectionPoint_surjective c
  obtain ⟨j, rfl⟩ := vertexIntersectionPoint_surjective d
  aesop

theorem vertexIntersectionUpper_monotone : Monotone vertexIntersectionUpper := by
  have h : ∀ i j,
      CoordinateFace (vertexIntersectionCoordinates i) (vertexIntersectionCoordinates j) →
      CoordinateFace (vertexIntersectionCoordinates (vertexIntersectionUpperIndex i))
        (vertexIntersectionCoordinates (vertexIntersectionUpperIndex j)) := by unfold CoordinateFace; decide
  intro c d hcd
  obtain ⟨i, rfl⟩ := vertexIntersectionPoint_surjective c
  obtain ⟨j, rfl⟩ := vertexIntersectionPoint_surjective d
  aesop

theorem vertexIntersectionLower_le c : vertexIntersectionLower c ≤ c := by
  have h : ∀ i, CoordinateFace
      (vertexIntersectionCoordinates (vertexIntersectionLowerIndex i))
      (vertexIntersectionCoordinates i) := by unfold CoordinateFace; decide
  obtain ⟨i, rfl⟩ := vertexIntersectionPoint_surjective c
  aesop

theorem vertexIntersectionLower_le_upper c :
    vertexIntersectionLower c ≤ vertexIntersectionUpper c := by
  have h : ∀ i, CoordinateFace
      (vertexIntersectionCoordinates (vertexIntersectionLowerIndex i))
      (vertexIntersectionCoordinates (vertexIntersectionUpperIndex i)) := by unfold CoordinateFace; decide
  aesop

theorem vertexIntersectionPoint_zero_le_upper c :
    vertexIntersectionPoint 0 ≤ vertexIntersectionUpper c := by
  have h : ∀ i, CoordinateFace (vertexIntersectionCoordinates 0)
      (vertexIntersectionCoordinates (vertexIntersectionUpperIndex i)) := by unfold CoordinateFace; decide
  aesop

/-- The actual intersection is acyclic in all augmented nerve degrees. -/
theorem vertexPuncture_intersection_acyclic :
    AcyclicIn (fun c => vertexPunctureLeft c ∧ vertexPunctureRight c) := by
  apply acyclicIn_of_subtype _ ⟨vertexIntersectionCell 0, vertexIntersectionCell_mem 0⟩
  intro c hc hcyc
  exact exists_bdry_eq_of_cycle_threeLeg vertexIntersectionLower vertexIntersectionUpper
    _ vertexIntersectionLower_monotone vertexIntersectionUpper_monotone
    vertexIntersectionLower_le vertexIntersectionLower_le_upper
    vertexIntersectionPoint_zero_le_upper c hc hcyc
