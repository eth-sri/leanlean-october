module

public import RequestProject.TopologicalSingular.TriangleSquareGeometry
public import RequestProject.TopologicalSingular.Pi2HurewiczHom

@[expose] public section

namespace FiniteChains.TopologicalSingular
open CategoryTheory AlgebraicTopology
open scoped Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

variable (tau : Simplex X 2)

section

variable (h : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x)
include h

theorem basedTriangle_eq_of_zero_coordinate
    (z : Domain 2) (i : Fin 3) (hi : z.val i = 0) : tau z = x := by
  obtain ⟨w, hw⟩ := domain_zero_coordinate_face z i hi
  have he := congrArg (fun f : Simplex X 1 => f w) (h i)
  change tau _ = x at he
  simp_all

/-- A triangle with all three faces at the basepoint is an actual based
square, by collapsing the upper triangle of the square onto an edge. -/
noncomputable def basedTriangleSquare : GenLoop (Fin 2) X x :=
  ⟨tau.comp squareToTriangle, by
    intro z hz
    obtain ⟨i, hi⟩ := squareToTriangle_boundary z hz
    apply basedTriangle_eq_of_zero_coordinate <;> assumption⟩

end

noncomputable def basedTriangleCycle (x : X) : Chain X 2 :=
  Finsupp.single tau 1 - Finsupp.single (ContinuousMap.const _ x) 1

variable (h : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x)
include h

theorem basedTriangleCycle_boundary :
    boundary 1 (basedTriangleCycle tau x) = 0 := by
  rw [basedTriangleCycle, map_sub, boundary_two_single, boundary_constant_two, h 0, h 1, h 2]
  abel

/-- Exact chain identity; no subdivision or comparison hypothesis is used. -/
theorem squareCycle_basedTriangleSquare :
    squareCycle (basedTriangleSquare tau h) = basedTriangleCycle tau x := by
  have he1 : simplexMap (basedTriangleSquare tau h).val 2 cubeTriangle1 = tau := by
    apply ContinuousMap.ext
    intro z
    change tau _ = tau z
    simp [squareToTriangle_triangle1]
  have he0 : simplexMap (basedTriangleSquare tau h).val 2 cubeTriangle0 =
      ContinuousMap.const (Domain 2) x := by
    apply ContinuousMap.ext
    intro z
    exact basedTriangle_eq_of_zero_coordinate tau h _ 1 (squareToTriangle_triangle0_zero z)
  rw [squareCycle, squareFundamentalChain, map_sub, map_single, map_single, he1, he0]
  rfl

end FiniteChains.TopologicalSingular
