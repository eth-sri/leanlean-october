/- Original assembly of the ported finite-box limits and the exact frozen cylinder bridge. -/
module

public import PottsDiscontinuity.FK.FrozenLimitBridge
public import PottsDiscontinuity.FK.FreeBoxLimit
public import PottsDiscontinuity.FK.WiredBoxLimits
public import PottsDiscontinuity.FK.BoundaryPartitionLaw

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.FK

noncomputable section

/-- The origin-centered ported box is exactly the frozen box. -/
theorem latticeBox_origin_eq_box (n : ℕ) : latticeBox (0, 0) n = box n := by
  simp [latticeBox, box, zero_sub, zero_add]

section
variable (θ : Parameters) (c : LatticeVertex) (r : ℕ)

/-- The generic frozen-law extension agrees with the ported free finite-box law. -/
theorem frozenExtendedProbabilityMeasure_free :
    frozenExtendedProbabilityMeasure θ 0 (boxConfiguration c r) =
      boxProbabilityMeasure θ c r := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((law (boxGraph c r) θ (frozenBoundaryCondition (latticeBox c r) 0)).map
    (boxConfiguration c r)).toMeasure =
    ((law (boxGraph c r) θ (BoundaryCondition.free ∅)).map (boxConfiguration c r)).toMeasure
  have hlaw : law (boxGraph c r) θ (frozenBoundaryCondition (latticeBox c r) 0) =
      law (boxGraph c r) θ (BoundaryCondition.free ∅) := by
    apply law_eq_of_boundary_partition_eq
    simp [frozenBoundaryCondition, BoundaryCondition.free]
  rw [hlaw]

end

variable {θ : Parameters} {μ : ProbabilityMeasure LatticeConfiguration}

/-- Every weak limit of the ported free origin-box laws has the exact frozen characterization. -/
theorem isRCInfiniteVolumeLimit_of_freeBox_tendsto
    (hμ : Tendsto (fun n => boxProbabilityMeasure θ (0, 0) n) atTop (𝓝 μ)) :
    IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ.toMeasure := by
  refine isRCInfiniteVolumeLimit_of_extended_tendsto θ 0
    (S := (fun n => latticeBox (0, 0) n)) latticeBox_origin_eq_box
    (ext := (fun n => boxConfiguration (0, 0) n)) ?_ μ ?_
  · intro n C f
    exact boxConfiguration_at (c := (0, 0)) n C f
  · assumption

/-- Every weak limit of the ported wired origin-box laws has the exact frozen characterization. -/
theorem isRCInfiniteVolumeLimit_of_wiredBox_tendsto
    (hμ : Tendsto (fun n => wiredBoxProbabilityMeasure θ (0, 0) n) atTop (𝓝 μ)) :
    IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ.toMeasure := by
  refine isRCInfiniteVolumeLimit_of_extended_tendsto θ 1
    (S := (fun n => latticeBox (0, 0) n)) latticeBox_origin_eq_box
    (ext := (fun n => wiredBoxConfiguration (0, 0) n)) ?_ μ ?_
  · intro n C f
    exact wiredBoxConfiguration_at (c := (0, 0)) n C f
  · assumption

/-- For independent interior edge probabilities and cluster weights at least one,
both frozen boundary conditions have infinite-volume limits. -/
theorem exists_isRCInfiniteVolumeLimit_interior (θ : Parameters) (i : Fin 2) :
    ∃ μ, IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ := by
  fin_cases i
  · obtain ⟨μ, hμ, _⟩ := Internal.freeBoxLimit_existsUnique (q := θ)
    exact ⟨μ.toMeasure, isRCInfiniteVolumeLimit_of_freeBox_tendsto
      (hμ (fun _ => (0, 0)) (fun n => n)
        origin_latticeBox_nested origin_latticeBox_exhaustive)⟩
  · obtain ⟨μ, hμ⟩ := wiredBoxProbabilityMeasure_exists_limit θ
    exact ⟨μ.toMeasure, isRCInfiniteVolumeLimit_of_wiredBox_tendsto hμ⟩

end
end PottsDiscontinuity.FK
