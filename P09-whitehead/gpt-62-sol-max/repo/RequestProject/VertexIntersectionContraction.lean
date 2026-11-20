module

public import RequestProject.VertexPunctureIntersection
public import RequestProject.NerveThreeLegContraction
public import RequestProject.NerveSupport

@[expose] public section

/-! An explicit contraction of the actual seven-cell intersection path. -/
namespace FiniteChains.Davis
open Comb Nerve

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
  obtain ⟨i, hi⟩ := vertexIntersection_classify c.1 c.2
  exact ⟨i, Subtype.ext hi.symm⟩

noncomputable def vertexIntersectionEquiv : Fin 7 ≃ VertexIntersection :=
  Equiv.ofBijective vertexIntersectionPoint ⟨vertexIntersectionPoint_injective, vertexIntersectionPoint_surjective⟩

private def lower : Fin 7 → Fin 7 := ![0, 1, 2, 3, 4, 3, 2]
private def upper : Fin 7 → Fin 7 := ![0, 1, 1, 4, 4, 4, 1]

private noncomputable def move (f : Fin 7 → Fin 7) : VertexIntersection → VertexIntersection :=
  vertexIntersectionEquiv ∘ f ∘ vertexIntersectionEquiv.symm

@[simp] private theorem move_point (f : Fin 7 → Fin 7) (i : Fin 7) :
    move f (vertexIntersectionEquiv i) = vertexIntersectionEquiv (f i) := by simp [move]

private theorem move_monotone {f : Fin 7 → Fin 7}
    (h : ∀ i j, CoordinateFace (vertexIntersectionCoordinates i) (vertexIntersectionCoordinates j) →
      CoordinateFace (vertexIntersectionCoordinates (f i)) (vertexIntersectionCoordinates (f j))) :
    Monotone (move f) := by
  intro a b hab
  obtain ⟨i, rfl⟩ := vertexIntersectionEquiv.surjective a
  obtain ⟨j, rfl⟩ := vertexIntersectionEquiv.surjective b
  simpa only [move_point] using (show vertexIntersectionEquiv (f i) ≤ vertexIntersectionEquiv (f j) from h i j hab)

private theorem move_le {f g : Fin 7 → Fin 7}
    (h : ∀ i, CoordinateFace (vertexIntersectionCoordinates (f i)) (vertexIntersectionCoordinates (g i))) :
    move f ≤ move g := fun a => h (vertexIntersectionEquiv.symm a)

/-- The actual intersection is acyclic in all augmented nerve degrees. -/
theorem vertexPuncture_intersection_acyclic :
    AcyclicIn (fun c : VertexPuncturedCube => vertexPunctureLeft c ∧ vertexPunctureRight c) := by
  apply acyclicIn_of_subtype _
  have hl : move lower ≤ move id := move_le (by unfold CoordinateFace; decide)
  have h0 : move (fun _ => 0) ≤ move upper := move_le (by unfold CoordinateFace; decide)
  have hid : move id = id := funext fun x => vertexIntersectionEquiv.apply_symm_apply x
  rw [hid] at hl
  exact exists_bdry_eq_of_cycle_threeLeg _ _ (vertexIntersectionEquiv 0)
    (move_monotone (by unfold CoordinateFace; decide)) (move_monotone (by unfold CoordinateFace; decide))
    (Or.inr hl) (Or.inl (move_le (by unfold CoordinateFace; decide))) (Or.inr h0)

end FiniteChains.Davis
