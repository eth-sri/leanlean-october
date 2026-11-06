
import GS.Topology.PuncturedSphereObstruction
import GS.NonmanifoldClosure.ChartRetractions
import GS.NonmanifoldClosure.RegularConeChart
import GS.NonmanifoldFinal.ConditionalGS
import GS.RestrictedNonmanifold.ConditionalReduction



/-!
# Unconditional topological nonmanifoldness of the cone and the GS family

The geometric retractions and charts are combined with the proved Brouwer
theorem and the proved nullhomotopy theorem for maps into larger spheres.
Neither a sphere-homology profile nor a cone-obstruction premise occurs in
the final statements. The original family and its induced topology are used.
-/

open GS.NonmanifoldObstruction GS.NonmanifoldFinal
open GS.NonmanifoldClosure

namespace GS.NonmanifoldTopology

/-- Restrict an actual chart to a punctured ball and use sphere domination. -/
theorem chart_dimension_of_sphereRetractions
    {X : Type} [TopologicalSpace X] {m n : ℕ}
    (c : OpenEuclideanChart X n) (x : X) (hx : x ∈ c.source)
    (O : Set X) (hO : IsOpen O) (hxO : x ∈ O)
    (hret : SphereRetractionsOn O x m) : n = m := by
  obtain ⟨b, hb⟩ := exists_centeredChart (c.restrict O hO) x ⟨hx,hxO⟩
  obtain ⟨p⟩ := hret b.source b.source_open b.source_point (fun _ h => (hb h).2)
  exact GS.Topology.sphere_retract_ball_dimension_of_fixedPoint m n b.radius_pos
    (transportSectionPair p (Homeomorph.refl _) b.punctured)



/-- A forced vertex dimension incompatible with nearby regular charts rules out a chart. -/
theorem not_euclidean_of_sphereRetractions
    {X : Type} [TopologicalSpace X] {x : X} {m : ℕ}
    (hret : SphereRetractionsOn Set.univ x m) (k : ℕ) (hmk : m ≠ k)
    (hregular : ∀ U : Set X, IsOpen U → x ∈ U →
      ∃ c : OpenEuclideanChart X k, ∃ y : X, y ∈ U ∧ y ∈ c.source) :
    ¬ EuclideanAt x := by
  intro he
  obtain ⟨n,c,hc⟩ := (euclideanAt_iff_chart x).mp he
  have hn := chart_dimension_of_sphereRetractions c x hc Set.univ isOpen_univ
    (Set.mem_univ _) hret
  obtain ⟨d,y,hyc,hyd⟩ := hregular c.source c.source_open hc
  exact hmk (hn.symm.trans (chart_dimension_of_sphereRetractions c y hyc d.source
    d.source_open hyd (d.sphereRetractions y hyd)))

/-- The rank-one vertex is singular for all finite coordinate sets of width at least two. -/
theorem cone_not_euclidean {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (hd : 2 ≤ Fintype.card κ) : ¬ EuclideanAt (productZero : ConeSpace ι κ) := by
  refine not_euclidean_of_sphereRetractions (m := Fintype.card ι+2) ?_
    (Fintype.card ι+Fintype.card κ+1) (by omega) ?_
  · intro U hU h0 _
    exact every_punctured_cone_open_has_standard_sphere_retract hd U hU h0
  · intro U hU h0
    obtain ⟨j⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card κ)
    obtain ⟨p,hp,hpc⟩ := GS.Topology.exists_regular 1  j U hU h0
    exact ⟨GS.Topology.rankPivotChart 1  j,p,hp,hpc⟩

end GS.NonmanifoldTopology
