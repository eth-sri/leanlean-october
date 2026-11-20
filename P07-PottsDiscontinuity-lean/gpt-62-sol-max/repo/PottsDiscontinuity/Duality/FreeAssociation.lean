module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.ConnectionEvents
public import PottsDiscontinuity.Duality.BoxDihedral
public import PottsDiscontinuity.FK.LimitTranslation
public import PottsDiscontinuity.FK.BoxLimits
public import PottsDiscontinuity.FK.FreeBoxPositiveAssociation
public import PottsDiscontinuity.Infra.CylinderUniqueness

/-! Positive association for actual, unbounded free connectivity events. -/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.Duality

open FK

export CorrLength (free_limit_eq_selected)

/-- FKG and concatenation for actual open connections. -/
theorem free_connection_mul_le (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) (u v w : LatticeVertex) :
    μ (connectionEvent u v) * μ (connectionEvent v w) ≤ μ (connectionEvent u w) := by
  simp only [connectionEvent_eq_finite]
  exact CorrLength.free_connection_mul_le θ μ hμ u v w

/-- Every lattice graph symmetry preserving all centered boxes preserves the
actual free infinite-volume measure. -/
theorem free_limit_map_latticeIso
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (e : squareLattice ≃g squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r) :
    μ.map (latticeConfigurationIsoHomeomorph e) = μ := by
  rw [free_limit_eq_selected θ μ hμ]
  exact congrArg ProbabilityMeasure.toMeasure
    (Internal.freeBoxLimit_latticeIso_invariant θ e hbox)

end PottsDiscontinuity.Duality
