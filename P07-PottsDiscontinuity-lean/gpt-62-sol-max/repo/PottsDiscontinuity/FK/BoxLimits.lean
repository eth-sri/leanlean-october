/- Original assembly of the ported finite-box limits and the exact frozen cylinder bridge. -/
module

public import PottsDiscontinuity.FK.FrozenLimitBridge
public import PottsDiscontinuity.FK.FreeBoxLimit
public import PottsDiscontinuity.FK.WiredBoxLimits
public import PottsDiscontinuity.FK.BoundaryPartitionLaw
public import PottsDiscontinuity.Infra.CylinderUniqueness

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.FK

noncomputable section

/-- The origin-centered ported box is exactly the frozen box. -/
theorem latticeBox_origin_eq_box (n : ℕ) : latticeBox (0, 0) n = box n := by
  simp [latticeBox, box]

/-- The generic frozen-law extension agrees with the ported free finite-box law. -/
theorem frozenExtendedProbabilityMeasure_free (θ : Parameters) (c : LatticeVertex) (r : ℕ) :
    frozenExtendedProbabilityMeasure θ (latticeBox c r) 0 (boxConfiguration c r) =
      boxProbabilityMeasure θ c r := by
  solve_by_elim

/-- Every weak limit of the ported free origin-box laws has the exact frozen characterization. -/
theorem isRCInfiniteVolumeLimit_of_freeBox_tendsto (θ : Parameters)
    (μ : ProbabilityMeasure LatticeConfiguration)
    (hμ : Tendsto (fun n => boxProbabilityMeasure θ (0, 0) n) atTop (𝓝 μ)) :
    IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ.toMeasure := by
  refine isRCInfiniteVolumeLimit_of_extended_tendsto θ 0
    (fun n => latticeBox (0, 0) n) latticeBox_origin_eq_box
    (fun n => boxConfiguration (0, 0) n) ?_ μ ?_
  · intro n C f
    exact boxConfiguration_at (0, 0) n C f
  solve_by_elim

/-- Every weak limit of the ported wired origin-box laws has the exact frozen characterization. -/
theorem isRCInfiniteVolumeLimit_of_wiredBox_tendsto (θ : Parameters)
    (μ : ProbabilityMeasure LatticeConfiguration)
    (hμ : Tendsto (fun n => wiredBoxProbabilityMeasure θ (0, 0) n) atTop (𝓝 μ)) :
    IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ.toMeasure := by
  refine isRCInfiniteVolumeLimit_of_extended_tendsto θ 1
    (fun n => latticeBox (0, 0) n) latticeBox_origin_eq_box
    (fun n => wiredBoxConfiguration (0, 0) n) ?_ μ ?_
  · intro n C f
    exact wiredBoxConfiguration_at (0, 0) n C f
  solve_by_elim

end
end PottsDiscontinuity.FK

namespace PottsDiscontinuity.RCInfinite

open FK

/-- The two actual finite-box laws, with their respective exterior extensions. -/
noncomputable def boxMeasure (θ : Parameters) (i : Fin 2) (c : LatticeVertex) (r : ℕ) :
    ProbabilityMeasure LatticeConfiguration :=
  if i = 0 then boxProbabilityMeasure θ c r else wiredBoxProbabilityMeasure θ c r

section

variable (θ : Parameters) (c : LatticeVertex) (r : ℕ)

@[simp] theorem boxMeasure_free :
    boxMeasure θ 0 c r = boxProbabilityMeasure θ c r := rfl

@[simp] theorem boxMeasure_wired :
    boxMeasure θ 1 c r = wiredBoxProbabilityMeasure θ c r := rfl

end

theorem boxMeasure_existsUnique (θ : Parameters) (i : Fin 2) :
    ∃! μ, WeakBoxLimit (boxMeasure θ i) μ := by
  fin_cases i
  · exact freeBoxLimit_existsUnique θ
  · exact wiredBoxLimit_existsUnique θ

theorem isRCInfiniteVolumeLimit_of_boxMeasure_tendsto (θ : Parameters) (i : Fin 2)
    (μ : ProbabilityMeasure LatticeConfiguration)
    (hμ : Tendsto (boxMeasure θ i (0, 0)) atTop (𝓝 μ)) :
    IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ := by
  fin_cases i
  · exact isRCInfiniteVolumeLimit_of_freeBox_tendsto θ μ hμ
  · exact isRCInfiniteVolumeLimit_of_wiredBox_tendsto θ μ hμ

theorem rc_limit_eq_of_weakBoxLimit {θ : Parameters} {i : Fin 2}
    {μ : Measure LatticeConfiguration} {ν : ProbabilityMeasure LatticeConfiguration}
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ) (hν : WeakBoxLimit (boxMeasure θ i) ν) :
    μ = ν.toMeasure :=
  rc_limit_unique θ.toP θ.toQ i μ ν.toMeasure hμ
    (isRCInfiniteVolumeLimit_of_boxMeasure_tendsto θ i ν hν.atOrigin)

end PottsDiscontinuity.RCInfinite

namespace PottsDiscontinuity.FK

open RCInfinite

/-- For independent interior edge probabilities and cluster weights at least one,
both frozen boundary conditions have infinite-volume limits. -/
theorem exists_isRCInfiniteVolumeLimit_interior (θ : Parameters) (i : Fin 2) :
    ∃ μ, IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ := by
  obtain ⟨μ, hμ, _⟩ := boxMeasure_existsUnique θ i
  exact ⟨μ.toMeasure, isRCInfiniteVolumeLimit_of_boxMeasure_tendsto θ i μ hμ.atOrigin⟩

end PottsDiscontinuity.FK
