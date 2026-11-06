module

public import GS.NonmanifoldObstruction.PuncturedNeighbourhood
public import GS.NonmanifoldClosure.TopologicalClosure

@[expose] public section


/-!
# Isolated-zero Euclidean retracts and punctured neighbourhoods

A continuous Euclidean retract whose projection vanishes only at the marked
point produces a sphere retract in every punctured open neighbourhood. This
criterion is applicable to Clifford contractions of rank-one matrix cones.
-/
noncomputable section
open GS.NonmanifoldObstruction GS.NonmanifoldFinal GS.NonmanifoldClosure
namespace GS.UnitaryTopology

structure IsolatedEuclideanRetract (X : Type*) [TopologicalSpace X]
    (x₀ : X) (m : ℕ) where
  sectionMap : Eucl m → X
  projectionMap : X → Eucl m
  section_continuous : Continuous sectionMap
  projection_continuous : Continuous projectionMap
  projection_section : ∀ x, projectionMap (sectionMap x) = x
  section_zero : sectionMap 0 = x₀
  projection_zero_iff : ∀ x, projectionMap x = 0 ↔ x = x₀

variable {X : Type} [TopologicalSpace X] {x₀ : X} {m : ℕ}

theorem IsolatedEuclideanRetract.punctured_sphere
    (r : IsolatedEuclideanRetract X x₀ m)
    (U : Set X) (hU : IsOpen U) (hx : x₀ ∈ U) :
    Nonempty (ContinuousSectionPair (UnitSphere (Fin m)) (PuncturedIn U x₀)) := by
  obtain ⟨V,hV,h0,hVsub⟩ := uniform_neighbourhood_of_compact_parameter
    (fun p : ℝ × UnitSphere (Fin m) => r.sectionMap (p.1 • p.2.val)) (by have := r.section_continuous; fun_prop)
    0 U hU (fun v => by simpa [r.section_zero] using hx)
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hV 0 h0
  have htV : δ/2 ∈ V := hball (by simp [abs_of_pos hδ]; linarith)
  have hne (p : PuncturedIn U x₀) : ‖r.projectionMap p.val‖ ≠ 0 := by
    simpa [r.projection_zero_iff] using p.property.2
  refine ⟨⟨fun v => ⟨r.sectionMap ((δ/2) • v.val), by grind, fun he => ?_⟩,
    fun x => ⟨‖r.projectionMap x.val‖⁻¹ • r.projectionMap x.val, by simp [norm_smul, hne]⟩,
    by have := r.section_continuous; fun_prop,
    by have := r.projection_continuous; fun_prop (disch := exact hne _), fun v => Subtype.ext ?_⟩⟩
  · have hp := congrArg r.projectionMap he
    rw [r.projection_section, (r.projection_zero_iff x₀).mpr rfl] at hp
    aesop
  · simp [r.projection_section, norm_smul, abs_of_pos hδ, smul_smul, hδ.ne']

/-- A regular chart of another dimension in every vertex neighbourhood excludes
a Euclidean chart at the vertex. Both ingredients are explicit geometric data. -/
theorem not_euclidean_of_retract_regular_charts
    (r : IsolatedEuclideanRetract X x₀ m) (k : ℕ) (hmk : m ≠ k)
    (hregular : ∀ U : Set X, IsOpen U → x₀ ∈ U →
      ∃ c : OpenEuclideanChart X k, ∃ x : X, x ∈ U ∧ x ∈ c.source) :
    ¬ EuclideanAt x₀ := by
  intro he
  obtain ⟨n,c,hc⟩ := (euclideanAt_iff_chart x₀).mp he
  obtain ⟨d,x,hxc,hxd⟩ := hregular c.source c.source_open hc
  have := GS.NonmanifoldTopology.chart_dimension_of_sphereRetractions c x₀ hc Set.univ isOpen_univ trivial
    fun U hU hx _ => r.punctured_sphere U hU hx
  have := GS.NonmanifoldTopology.dimensions_of_overlapping_charts c d x hxc hxd
  grind

end GS.UnitaryTopology
