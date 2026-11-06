import RequestProject.TopologicalSingular.VertexEdgeNormalization
import RequestProject.TopologicalSingular.SingularEdgeNullHomotopy
noncomputable section


namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

def edgeVertexNullHomotopy x (tau : Simplex X 1) :=
  Classical.choice (singularEdge_nullhomotopic x _
    (edgeVertexNormalized_vertex x tau 0) (edgeVertexNormalized_vertex x tau 1))

def normalizedEdgeHomotopy (x : X) (tau : Simplex X 1) :=
  (edgeVertexHomotopy x tau).trans (edgeVertexNullHomotopy x tau).toHomotopy

def normalizationVertexPath (x a : X) :=
  (PathConnectedSpace.somePath a x).trans (Path.refl x)

/-- Endpoint motion depends only on the original point, for all singular
edges simultaneously; this is the coherence needed for triangle boundaries. -/
theorem normalizedEdgeHomotopy_boundary x (tau : Simplex X 1) t
    z (hz : z ∈ simplexBoundary 1) :
    normalizedEdgeHomotopy x tau (t, z) = normalizationVertexPath x (tau z) t := by
  rw [normalizedEdgeHomotopy, ContinuousMap.Homotopy.trans_apply,
    normalizationVertexPath, Path.trans_apply]
  split_ifs
  · exact edgeVertexHomotopy_boundary x tau _ z hz
  · exact (edgeVertexNullHomotopy x tau).eq_snd _ hz
