import RequestProject.SquareBoundary
import RequestProject.TopologicalSingular.SingularPathHomotopy
import RequestProject.TopologicalSingular.RelativeSingularMaps
noncomputable section


namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology

/-- Coordinate identification used by the actual `GenLoop (Fin 2)` model. -/
def squareCoordinates : C(I × I, Fin 2 → I) where
  toFun z := ![z.1, z.2]
  continuous_toFun := by
    fun_prop

def cubeTriangle0 : Simplex (Fin 2 → I) 2 := squareCoordinates.comp squareTriangle0
def cubeTriangle1 : Simplex (Fin 2 → I) 2 := squareCoordinates.comp squareTriangle1

def cubeEdge (i : Fin 2) (v : I) : Simplex (Fin 2 → I) 1 :=
  ⟨fun z => Whitehead.squareEdge i v (stdSimplexHomeomorphUnitInterval z),
    (Whitehead.squareEdge_continuous i v).comp stdSimplexHomeomorphUnitInterval.continuous⟩

theorem cubeEdge_boundary i v (hv : v = 0 ∨ v = 1) z :
    cubeEdge i v z ∈ Cube.boundary (Fin 2) := by
  refine ⟨i, ?_⟩
  simpa [cubeEdge, Whitehead.squareEdge] using hv

theorem cubeTriangle_faces :
    face 0 cubeTriangle0 = cubeEdge 1 1 ∧ face 2 cubeTriangle0 = cubeEdge 0 0 ∧
    face 0 cubeTriangle1 = cubeEdge 0 1 ∧ face 2 cubeTriangle1 = cubeEdge 1 0 ∧
    face 1 cubeTriangle0 = face 1 cubeTriangle1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply ContinuousMap.ext
    intro z
    change squareCoordinates (squareTriangle0 (stdSimplex.map (SimplexCategory.δ (0)) z)) = _
    rw [(squareTriangle0_faces z).1]
    funext i
    fin_cases i <;> simp [squareCoordinates, cubeEdge, Whitehead.squareEdge]
  · apply ContinuousMap.ext
    intro z
    change squareCoordinates (squareTriangle0 (stdSimplex.map (SimplexCategory.δ (2)) z)) = _
    rw [(squareTriangle0_faces z).2.2]
    funext i
    fin_cases i <;> simp [squareCoordinates, cubeEdge, Whitehead.squareEdge]
  · apply ContinuousMap.ext
    intro z
    change squareCoordinates (squareTriangle1 (stdSimplex.map (SimplexCategory.δ (0)) z)) = _
    rw [(squareTriangle1_faces z).1]
    funext i
    fin_cases i <;> simp [squareCoordinates, cubeEdge, Whitehead.squareEdge]
  · apply ContinuousMap.ext
    intro z
    change squareCoordinates (squareTriangle1 (stdSimplex.map (SimplexCategory.δ (2)) z)) = _
    rw [(squareTriangle1_faces z).2.2]
    funext i
    fin_cases i <;> simp [squareCoordinates, cubeEdge, Whitehead.squareEdge]
  · apply ContinuousMap.ext
    intro z
    change squareCoordinates (squareTriangle0 (stdSimplex.map (SimplexCategory.δ (1)) z)) =
      squareCoordinates (squareTriangle1 (stdSimplex.map (SimplexCategory.δ (1)) z))
    rw [(squareTriangle0_faces z).2.1, (squareTriangle1_faces z).2.1]

/-- The two oriented triangles making up the parameter square. -/
def squareFundamentalChain : Chain (Fin 2 → I) 2 :=
  Finsupp.single cubeTriangle1 1 - Finsupp.single cubeTriangle0 1

theorem squareFundamentalChain_boundary : boundary 1 squareFundamentalChain =
    Finsupp.single (cubeEdge 0 1) 1 + Finsupp.single (cubeEdge 1 0) 1 -
      Finsupp.single (cubeEdge 1 1) 1 - Finsupp.single (cubeEdge 0 0) 1 := by
  simp [squareFundamentalChain, map_sub, boundary_two_single,
    cubeTriangle_faces.1, cubeTriangle_faces.2.1, cubeTriangle_faces.2.2.1,
    cubeTriangle_faces.2.2.2.1, cubeTriangle_faces.2.2.2.2]
  abel

theorem squareFundamentalChain_boundary_supported :
    boundary 1 squareFundamentalChain ∈ subChains (Cube.boundary (Fin 2)) 1 := by
  rw [squareFundamentalChain_boundary]
  apply Submodule.sub_mem
  · apply Submodule.sub_mem
    · apply Submodule.add_mem
      · exact single_mem_subChains _ 1 _ 1 (cubeEdge_boundary 0 1 (Or.inr rfl))
      · exact single_mem_subChains _ 1 _ 1 (cubeEdge_boundary 1 0 (Or.inl rfl))
    · exact single_mem_subChains _ 1 _ 1 (cubeEdge_boundary 1 1 (Or.inr rfl))
  · exact single_mem_subChains _ 1 _ 1 (cubeEdge_boundary 0 0 (Or.inl rfl))

universe u v
variable {X : Type u} [TopologicalSpace X] {x : X}

def squareCycle (p : GenLoop (Fin 2) X x) :=
  map p.val 2 squareFundamentalChain

theorem squareCycle_boundary (p : GenLoop (Fin 2) X x) : boundary 1 (squareCycle p) = 0 := by
  have he (i : Fin 2) (v : I) (hv : v = 0 ∨ v = 1) :
      simplexMap p.val 1 (cubeEdge i v) = ContinuousMap.const _ x := by
    apply ContinuousMap.ext
    intro z
    exact GenLoop.boundary p _ (cubeEdge_boundary i v hv z)
  simp [squareCycle, ← map_boundary, squareFundamentalChain_boundary, map_sub, map_add, map_single, he 0 1 (Or.inr rfl), he 1 0 (Or.inl rfl), he 1 1 (Or.inr rfl), he 0 0 (Or.inl rfl)]

theorem squareCycle_const : squareCycle (GenLoop.const (N := Fin 2) (x := x)) = 0 := by
  rw [squareCycle, squareFundamentalChain, map_sub, map_single, map_single]
  exact sub_self _
