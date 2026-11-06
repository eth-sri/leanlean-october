module

public import RequestProject.TopologicalSingular.TetrahedronSquareDisks
public import RequestProject.TopologicalSingular.SimplexLinearHomotopy

@[expose] public section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
variable {X : Type u} [TopologicalSpace X] {x : X}

theorem basedTetrahedron_eq_of_two_zero_coordinates (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x)
    (z : Domain 3) (i j : Fin 4) (hij : i ≠ j) (hi : z.val i = 0) (hj : z.val j = 0) :
    tau z = x := by
  obtain ⟨w, hw⟩ := domain_zero_coordinate_face z i hi
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
  have hz : w.val k = 0 := by
    rw [← simplex_face_coordinate_succAbove i w k, hk, hw, hj]
  obtain ⟨q, hq⟩ := domain_zero_coordinate_face w k hz
  have he := congrArg (fun f : Simplex X 1 => f q) (hedge i k)
  simpa only [face_apply, hq, hw, ContinuousMap.const_apply] using he

end FiniteChains.TopologicalSingular
