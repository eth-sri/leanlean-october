import RequestProject.TopologicalSingular.PointedSingularTriangle
import RequestProject.Tac


bwd

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
variable {X : Type} [TopologicalSpace X] {x : X}

theorem stickSimplex_isQuotientMap d : Topology.IsQuotientMap (stickSimplex d) :=
  Topology.IsQuotientMap.of_surjective_continuous (stickSimplex_surjective d)
    (stickSimplex d).continuous

/-- The only identifications made by stick coordinates occur on the boundary,
where a based cubical map is constant. -/
theorem genLoop_constant_on_stick_fiber d (p : GenLoop (Fin d) X x)
    t u (h : stickSimplex d t = stickSimplex d u) : p t = p u := by
  have hbd : t ∈ Cube.boundary _ ↔ u ∈ Cube.boundary _ := by
    simp [← stickSimplex_mem_bdry_iff, h]
  by_cases ht : t ∈ Cube.boundary _
  · rw [GenLoop.boundary p t ht, GenLoop.boundary p u (hbd.mp ht)]
  · exact congrArg p (stickSimplex_injective_of_not_mem_boundary d t u ht
      (by simp_all) h)

/-- Every actual based square factors continuously through the stick-coordinate
triangle, exactly rather than merely up to free homotopy. -/
theorem pointed_triangle_stick_represents_square p :
    ∃ a : PointedSingularTriangle X x, basedTriangleStickSquare a.map a.based = p := by
  let f := fun z => p (stickSimplex_surjective 2 z).choose
  have hf (t : Fin 2 → I) : f (stickSimplex 2 t) = p t :=
    genLoop_constant_on_stick_fiber 2 p _ t
      (by grind)
  have hc := (stickSimplex_isQuotientMap 2).continuous_iff.mpr (by
    have he : f ∘ stickSimplex 2 = p := funext hf
    rw [he]
    exact p.val.continuous)
  let tau : Simplex X 2 := by tauto
  have hbased : ∀ i : Fin 3, face i tau = ContinuousMap.const _ x := by
    intro i
    apply ContinuousMap.ext
    intro z
    apply GenLoop.boundary p
    apply (stickSimplex_mem_bdry_iff 2 _).mp
    rw [(stickSimplex_surjective 2 _).choose_spec]
    exact ⟨i, simplex_face_coordinate_zero i z⟩
  refine ⟨⟨tau, hbased⟩, ?_⟩
  aesop

theorem pointed_triangle_represents_pi2 p :
    ∃ a : PointedSingularTriangle X x,
      a.pi2 = Additive.ofMul (Quotient.mk _ p) := by
  cases' pointed_triangle_stick_represents_square p with a ha
  have h := basedTriangleStickSquare_pi2_eq a.map a.based
  aesop

theorem pointed_triangle_pi2_surjective :
    Function.Surjective (PointedSingularTriangle.pi2 (X := X) (x := x)) := by
  intro q
  cases' Quotient.exists_rep q.toMul with p hp
  cases' pointed_triangle_represents_pi2 p with a ha
  aesop
