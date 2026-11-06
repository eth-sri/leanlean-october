module

public import GS.Topology.PuncturedSphereObstruction
public import GS.NonmanifoldClosure.ChartRetractions
public import GS.NonmanifoldClosure.RegularConeChart
public import GS.NonmanifoldFinal.ConditionalGS
public import GS.Nonmanifold.SkewCoordinates
public import GS.NonmanifoldFinal.EuclideanTransport
public import GS.NonmanifoldFinal.FiniteCoordinates
public import GS.Specifications
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section



/-!
# Unconditional topological nonmanifoldness of the cone and the GS family

The geometric retractions and charts are combined with the proved Brouwer
theorem and the proved nullhomotopy theorem for maps into larger spheres.
Neither a sphere-homology profile nor a cone-obstruction premise occurs in
the final statements. The original family and its induced topology are used.
-/

noncomputable section

open Matrix GS GS.Nonmanifold GS.NonmanifoldObstruction GS.NonmanifoldFinal
open GS.NonmanifoldClosure

namespace GS.NonmanifoldTopology

section
variable {X : Type} [TopologicalSpace X] {m n : ℕ} (c : OpenEuclideanChart X n)
/-- Restrict an actual chart to a punctured ball and use sphere domination. -/
theorem chart_dimension_of_sphereRetractions
    (x : X) (hx : x ∈ c.source)
    (O : Set X) (hO : IsOpen O) (hxO : x ∈ O)
    (hret : SphereRetractionsOn O x m) : n = m := by
  obtain ⟨b, hb⟩ := exists_centeredChart_within c x hx O hO hxO
  obtain ⟨p⟩ := hret b.source b.source_open b.source_point (by grind)
  exact GS.Topology.sphere_retract_ball_dimension m n b.radius_pos
    (transportSectionPair p (Homeomorph.refl _) b.punctured)

/-- The dimensions of two overlapping Euclidean charts agree. -/
theorem dimensions_of_overlapping_charts
    (d : OpenEuclideanChart X m)
    (x : X) (hx : x ∈ c.source) (hy : x ∈ d.source) : n = m :=
  chart_dimension_of_sphereRetractions c x hx d.source d.source_open hy
    (d.sphereRetractions x hy)

end

/-- No Euclidean open chart exists at the vertex, for every width d ≥ 2. -/
theorem cone_not_euclidean (e d : ℕ) (hd : 2 ≤ d) :
    ¬ EuclideanAt (productZero : ConeSpace (Fin e) (Fin d)) := by
  intro hE
  obtain ⟨n, c, hc⟩ := (euclideanAt_iff_chart _).mp hE
  obtain ⟨p, hpc, hpr⟩ := exists_regular_in_open (⟨0, by omega⟩ : Fin d) c.source c.source_open hc
  have := chart_dimension_of_sphereRetractions c productZero hc Set.univ isOpen_univ trivial
    fun U hU h0 _ => every_punctured_cone_open_has_standard_sphere_retract (ι := Fin e) (by simp_all) U hU h0
  have := dimensions_of_overlapping_charts c (pivotProductChart (ι := Fin e) _) p hpc hpr
  simp_all
  omega

/-- The unchanged standalone cone specification is proved without an input premise. -/
theorem coneProductNonManifold : GS.Specifications.ConeProductNonManifoldGoal := fun d e hd hE =>
  cone_not_euclidean e d (by omega) ((euclideanAt_homeomorph flattenConeProduct productZero).mpr
    ((euclideanAtSubset_iff _ _ hE.1).mp hE))

end GS.NonmanifoldTopology
