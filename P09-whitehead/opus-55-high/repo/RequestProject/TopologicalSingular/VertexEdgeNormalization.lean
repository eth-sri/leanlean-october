import RequestProject.TopologicalSingular.SimplexBoundaryGluing
import RequestProject.Tac
noncomputable section


bwd

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]

def vertexNormalizationHomotopy (x : X) (tau : Simplex X 0) :
    tau.Homotopy (ContinuousMap.const (Domain 0) x) where
  toFun w := PathConnectedSpace.somePath (tau (stdSimplex.vertex 0)) x w.1
  continuous_toFun := (PathConnectedSpace.somePath _ _).continuous.comp continuous_fst
  map_zero_left z := by
    rw [Path.source]
    apply congrArg tau
    apply Subtype.ext
    funext i
    have hz := z.property.2
    simpa [stdSimplex.vertex, show i = 0 by omega] using hz.symm
  map_one_left _ := Path.target _

theorem vertexNormalizationHomotopy_apply x (tau : Simplex X 0) t z :
    vertexNormalizationHomotopy x tau (t, z) = PathConnectedSpace.somePath (tau z) x t := by
  have hz : stdSimplex.vertex 0 = z :=
    by
      apply Subtype.ext
      funext i
      have hz := z.property.2
      simpa [stdSimplex.vertex, show i = 0 by omega] using hz.symm
  aesop

/-- Endpoint motion for every edge is chosen from the original endpoint
itself, so different edges incident at that endpoint move it identically. -/
theorem edgeVertexNormalization_exists x (tau : Simplex X 1) :
    ∃ g : Simplex X 1, ∃ F : tau.Homotopy g,
      ∀ t z, z ∈ simplexBoundary 1 →
        F (t, z) = PathConnectedSpace.somePath (tau z) x t := by
  obtain ⟨g, F, hF⟩ := simplex_face_homotopy_extension tau
    _
    (by
      intro i j t z w h
      change vertexNormalizationHomotopy x (face i tau) (t, z) =
        vertexNormalizationHomotopy x (face j tau) (t, w)
      grind [vertexNormalizationHomotopy_apply, face_apply])
    (by simp)
  refine ⟨g, F, ?_⟩
  intro t z hz
  cases' hz with i hi
  cases' domain_zero_coordinate_face z i hi with w hw
  rw [← hw, hF]
  exact vertexNormalizationHomotopy_apply x _ t w

def edgeVertexNormalized (x : X) (tau : Simplex X 1) :=
  (edgeVertexNormalization_exists x tau).choose

def edgeVertexHomotopy x (tau : Simplex X 1) :
    tau.Homotopy (edgeVertexNormalized x tau) :=
  (edgeVertexNormalization_exists x tau).choose_spec.choose

theorem edgeVertexHomotopy_boundary x (tau : Simplex X 1) t
    z (hz : z ∈ simplexBoundary 1) :
    edgeVertexHomotopy x tau (t, z) = PathConnectedSpace.somePath (tau z) x t :=
  (edgeVertexNormalization_exists x tau).choose_spec.choose_spec t z hz

theorem simplexOne_vertex_mem_boundary (i : Fin 2) :
    stdSimplex.vertex i ∈ simplexBoundary 1 := by
  fin_cases i
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

theorem edgeVertexNormalized_vertex x (tau : Simplex X 1) (i : Fin 2) :
    edgeVertexNormalized x tau (stdSimplex.vertex i) = x := by
  have he := edgeVertexHomotopy_boundary x tau 1 _ (simplexOne_vertex_mem_boundary i)
  simp_all
