module

public import RequestProject.TopologicalSingular.PointedSingularTriangle

@[expose] public section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
variable {X : Type} [TopologicalSpace X] {x : X}

variable (d : ℕ)

theorem stickSimplex_isQuotientMap : Topology.IsQuotientMap (stickSimplex d) :=
  Topology.IsQuotientMap.of_surjective_continuous (stickSimplex_surjective d)
    (stickSimplex d).continuous

/-- The only identifications made by stick coordinates occur on the boundary,
where a based cubical map is constant. -/
theorem genLoop_constant_on_stick_fiber (p : GenLoop _ X x)
    (t u : Fin d → I) (h : stickSimplex d t = stickSimplex d u) : p t = p u := by
  have hbd : t ∈ Cube.boundary _ ↔ u ∈ Cube.boundary _ := by
    rw [← stickSimplex_mem_bdry_iff, ← stickSimplex_mem_bdry_iff, h]
  by_cases ht : t ∈ Cube.boundary _
  · simp_all [GenLoop.boundary]
  · grind [stickSimplex_injective_of_not_mem_boundary]

variable (p : GenLoop (Fin 2) X x)

/-- Every actual based square factors continuously through the stick-coordinate
triangle, exactly rather than merely up to free homotopy. -/
theorem pointed_triangle_stick_represents_square :
    ∃ a : PointedSingularTriangle X x, basedTriangleStickSquare a.map a.based = p := by
  let f := fun z => p (stickSimplex_surjective 2 z).choose
  have hf (t : Fin 2 → I) :=
    genLoop_constant_on_stick_fiber 2 p _ t
      (stickSimplex_surjective 2 (stickSimplex 2 t)).choose_spec
  have hc := (stickSimplex_isQuotientMap 2).continuous_iff.mpr (by
    have he : f ∘ stickSimplex 2 = p := funext hf
    rw [he]
    exact p.val.continuous)
  let tau : Simplex X 2 := ⟨f, hc⟩
  have hbased : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x := by
    intro i
    apply ContinuousMap.ext
    intro z
    apply GenLoop.boundary p; apply (stickSimplex_mem_bdry_iff 2 _).mp; rw [(stickSimplex_surjective 2 _).choose_spec]; exact ⟨i, simplex_face_coordinate_zero i z⟩
  refine ⟨⟨tau, hbased⟩, ?_⟩
  apply GenLoop.ext
  exact hf

theorem pointed_triangle_represents_pi2 :
    ∃ a : PointedSingularTriangle X x,
      a.pi2 = Additive.ofMul (Quotient.mk _ p) := by
  obtain ⟨a, ha⟩ := pointed_triangle_stick_represents_square p
  have h := basedTriangleStickSquare_pi2_eq a.map a.based
  aesop

theorem pointed_triangle_pi2_surjective :
    Function.Surjective (PointedSingularTriangle.pi2 (X := X) (x := x)) := by
  intro q
  obtain ⟨p, hp⟩ := Quotient.exists_rep q.toMul
  obtain ⟨a, ha⟩ := pointed_triangle_represents_pi2 p <;> aesop

end FiniteChains.TopologicalSingular
