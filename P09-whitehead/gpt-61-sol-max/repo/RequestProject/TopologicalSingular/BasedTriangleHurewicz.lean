import Mathlib.Tactic

import RequestProject.TopologicalSingular.TriangleSquareGeometry
import RequestProject.TopologicalSingular.Pi2HurewiczHom

namespace FiniteChains.TopologicalSingular


variable {X : Type u} [TopologicalSpace X] {x : X}

  (tau : Simplex X 2)
variable (h : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x)
include h in
theorem basedTriangle_eq_of_zero_coordinate 
    
    (z : Domain 2) (i : Fin 3) (hi : z.val i = 0) : tau z = x := by
  obtain ⟨w, hw⟩ := domain_zero_coordinate_face z i hi
  have he := congrArg (fun f : Simplex X 1 => f w) (h i)
  change tau (stdSimplex.map (SimplexCategory.δ i) w) = x at he
  rwa [hw] at he

include h in
/-- A triangle with all three faces at the basepoint is an actual based
square, by collapsing the upper triangle of the square onto an edge. -/
noncomputable def basedTriangleSquare 
     : GenLoop (Fin 2) X x :=
  ⟨tau.comp squareToTriangle, by
    intro z hz
    obtain ⟨i, hi⟩ := squareToTriangle_boundary z hz
    exact basedTriangle_eq_of_zero_coordinate tau h _ i hi⟩

noncomputable def basedTriangleCycle  (x : X) : Chain X 2 :=
  Finsupp.single tau 1 - Finsupp.single (ContinuousMap.const (Domain 2) x) 1

include h in
theorem basedTriangleCycle_boundary 
     :
    boundary 1 (basedTriangleCycle tau x) = 0 := by
  rw [basedTriangleCycle, map_sub, boundary_two_single, boundary_constant_two, h 0, h 1, h 2]
  abel

include h in
/-- Exact chain identity; no subdivision or comparison hypothesis is used. -/
theorem squareCycle_basedTriangleSquare 
     :
    squareCycle (basedTriangleSquare tau h) = basedTriangleCycle tau x := by
  have he1 : simplexMap (basedTriangleSquare tau h).val 2 cubeTriangle1 = tau := by
    apply ContinuousMap.ext
    intro z
    change tau (squareToTriangle (cubeTriangle1 z)) = tau z
    rw [squareToTriangle_triangle1]
  have he0 : simplexMap (basedTriangleSquare tau h).val 2 cubeTriangle0 =
      ContinuousMap.const (Domain 2) x := by
    apply ContinuousMap.ext
    intro z
    exact basedTriangle_eq_of_zero_coordinate tau h _ 1 (squareToTriangle_triangle0_zero z)
  rw [squareCycle, squareFundamentalChain, map_sub, map_single, map_single, he1, he0]
  rfl

end FiniteChains.TopologicalSingular







