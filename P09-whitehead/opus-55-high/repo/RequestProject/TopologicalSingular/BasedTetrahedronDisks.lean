import RequestProject.TopologicalSingular.TetrahedronSquareDisks
import RequestProject.TopologicalSingular.SimplexLinearHomotopy


namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

theorem basedTetrahedron_eq_of_two_zero_coordinates (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x)
    z (i j : Fin 4) (hij : i ≠ j) (hi : z.val i = 0) (hj : z.val j = 0) :
    tau z = x := by
  cases' domain_zero_coordinate_face z i hi with w hw
  cases' Fin.exists_succAbove_eq hij.symm with k hk
  have hz : w.val k = 0 := by
    rw [← simplex_face_coordinate_succAbove i w k, hk, hw, hj]
  cases' domain_zero_coordinate_face w k hz with q hq
  have he := congrArg (· q) (hedge i k)
  simpa [face_apply, hq, hw, ContinuousMap.const_apply] using he
