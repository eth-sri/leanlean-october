module

public import GS.NonmanifoldFinal.FiniteCoordinates
public import GS.NonmanifoldFinal.EuclideanTransport
public import GS.Specifications

@[expose] public section



/-!
# Exact final GS reduction -- CONDITIONAL, not the finished theorem

The sole additional hypothesis is the old, unchanged, standalone
GS.Specifications.ConeProductNonManifoldGoal. It is not proved in this file.
All GS-specific local coverage, membership, coordinate, and chart transport
steps are supplied by the imported, compiler-checked proof scripts.
This declaration must NEVER be reported as an
unconditional proof of GS.Specifications.NonManifoldGoal.
-/
noncomputable section
open Matrix GS GS.Nonmanifold GS.NonmanifoldCompletion GS.NonmanifoldObstruction
namespace GS.NonmanifoldFinal

/-- The original cone goal applies to the actual independent GS coordinates. -/
theorem model_not_euclidean_of_cone_goal
    (hCone : GS.Specifications.ConeProductNonManifoldGoal)
    (q : ℕ) (hq : 3 ≤ q) : ¬ EuclideanAt (modelCoordinatesZero q) := by
  intro hModel
  refine hCone _ (Fintype.card (FreeIndex q)) (three_le_card_upperIndex q hq) ((euclideanAtSubset_iff _ (0,0) (by simp)).mpr ?_)
  convert (euclideanAt_homeomorph ((modelToFin q).trans flattenConeProduct) _).mp hModel
    <;> aesop

end GS.NonmanifoldFinal
