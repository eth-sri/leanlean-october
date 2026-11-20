module

public import RequestProject.QCubeFacets
public import RequestProject.CutSurfaceSpine

@[expose] public section

/-! Fixed coordinate facets and the actual quotient-cube coefficient boundary. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [Fintype V] {A : CommRel V}

theorem qCubeToCoordinate_injective : Function.Injective (qCubeToCoordinate (A := A)) := by
  intro c d h
  apply qCubeCoordinateEquiv.injective
  exact Subtype.ext h

omit [Fintype V] in
/-- Freeing the fixed coordinate of an actual facet recovers its actual cube. -/
theorem qCubeFacet_coordinate_free (c : QCube A) (v : V) (hv : v ∈ c.spx)
    (s : ZMod 2) :
    Function.update (qCubeToCoordinate (qCubeFacet c v s)) v CubeCoord.free =
      qCubeToCoordinate c := by
  funext x
  by_cases hx : x = v
  · simp_all [qCubeToCoordinate, hv]
  · simp [qCubeToCoordinate, qCubeFacet, hx]

variable (g : Cube V) (c : QCube A) (v : V)

/-- A nonfree coordinate that frees to a given cube lies in that cube's free set. -/
theorem coordinate_update_free_mem
    (he : Function.update g v CubeCoord.free = qCubeToCoordinate c) : v ∈ c.spx := by
  have hfree : qCubeToCoordinate c v = CubeCoord.free := by simpa using (congrFun he v).symm
  exact (freeSet_qCubeToCoordinate c) ▸ mem_freeSet.mpr hfree

omit [Fintype V] in
/-- Every nonfree coordinate cube that frees to an actual cube is its actual fixed facet. -/
theorem coordinate_update_free_facet
    (hv : g v ≠ CubeCoord.free)
    (he : Function.update g v CubeCoord.free = qCubeToCoordinate c) :
    ∃ s : ZMod 2, g = qCubeToCoordinate (qCubeFacet c v s) := by
  have hother (x : V) (hx : x ≠ v) : g x = qCubeToCoordinate c x := by
    have h := congrFun he x
    simp_all
  cases hgv : g v with
  | free => simp_all
  | pos =>
      refine ⟨0, ?_⟩
      rw [qCubeFacet_coordinate_zero] <;> grind
  | neg =>
      refine ⟨1, ?_⟩
      rw [qCubeFacet_coordinate_one] <;> grind

variable [LinearOrder V]

variable (c : QCube A)

/-- The coefficient of any actual fixed facet in the collapse's cubical boundary is
exactly its coordinate incidence. -/
theorem cubeBdry_actual_facet (v : V) (hv : v ∈ c.spx) (s : ZMod 2) :
    cubeBdry (qCubeToCoordinate c) (Sum.inl (qCubeToCoordinate (qCubeFacet c v s))) =
      incid (qCubeToCoordinate (qCubeFacet c v s)) v := by
  classical
  let g := qCubeToCoordinate (qCubeFacet c v s)
  have hfixed : g v ≠ CubeCoord.free := by
    by_cases hs : s = 0 <;> simp [g, qCubeToCoordinate, qCubeFacet, hs]
  have he := qCubeFacet_coordinate_free c v hv s
  rw [cubeBdry_inl, Finset.sum_eq_single v]
  · simp_all
  · grind [update_free_injective]
  · grind

/-- The collapse's ordinary cubical boundary has no coefficient outside actual facets. -/
theorem cubeBdry_zero_off_actual_facets (g : Cube V)
    (hg : ∀ v ∈ c.spx, ∀ s : ZMod 2, g ≠ qCubeToCoordinate (qCubeFacet c v s)) :
    cubeBdry (qCubeToCoordinate c) (Sum.inl g) = 0 := by
  classical
  apply Finset.sum_eq_zero
  grind [coordinate_update_free_facet, coordinate_update_free_mem]

end FiniteChains.Davis
