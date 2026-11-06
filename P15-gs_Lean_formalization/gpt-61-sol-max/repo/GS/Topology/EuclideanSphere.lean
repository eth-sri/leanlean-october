
import Mathlib.Analysis.InnerProductSpace.PiL2



/-!
# Shared Euclidean sphere type

The definition is moved verbatim from NonmanifoldFinal/SphereCoordinates, with
unchanged namespace and type. It allows homology of ordinary balls and spheres
to be checked without importing the GS normalization/local-model construction.
-/

namespace GS.NonmanifoldFinal

abbrev UnitSphere (κ : Type*) [Fintype κ] :=
  {x : EuclideanSpace ℝ κ // x ∈ Metric.sphere 0 1}

end GS.NonmanifoldFinal
