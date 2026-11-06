import Mathlib.Tactic

import RequestProject.TopologicalSingular.VertexEdgeNormalization
import RequestProject.TopologicalSingular.SingularEdgeNullHomotopy

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

  (x : X)
  (tau : Simplex X 1)
noncomputable def edgeVertexNullHomotopy    :=
  Classical.choice (singularEdge_nullhomotopic x (edgeVertexNormalized x tau)
    (edgeVertexNormalized_vertex x tau 0) (edgeVertexNormalized_vertex x tau 1))

noncomputable def normalizedEdgeHomotopy    :=
  (edgeVertexHomotopy x tau).trans (edgeVertexNullHomotopy x tau).toHomotopy

noncomputable def normalizationVertexPath (x a : X)  :=
  (PathConnectedSpace.somePath a x).trans (Path.refl x)

/-- Endpoint motion depends only on the original point, for all singular
edges simultaneously; this is the coherence needed for triangle boundaries. -/
theorem normalizedEdgeHomotopy_boundary   (t : I)
    (z : Domain 1) (hz : z ∈ simplexBoundary 1) :
    normalizedEdgeHomotopy x tau (t, z) = normalizationVertexPath x (tau z) t := by
  rw [normalizedEdgeHomotopy, ContinuousMap.Homotopy.trans_apply,
    normalizationVertexPath, Path.trans_apply]
  split_ifs
  · simp_all [FiniteChains.TopologicalSingular.edgeVertexHomotopy_boundary]
  · exact (edgeVertexNullHomotopy x tau).eq_snd _ hz

end FiniteChains.TopologicalSingular
