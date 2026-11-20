module

public import PottsDiscontinuity.Potts.GhostCylinderPartition
public import PottsDiscontinuity.Potts.ESCylinderLaw
public import PottsDiscontinuity.Potts.SpinObservation
public import PottsDiscontinuity.Potts.PottsLimitConstruction

/-! Literal positive-boundary Potts limits and merged Edwards–Sokal colouring. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section

theorem wired_potts_cylinder_tendsto (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ))
    (φ : ProbabilityMeasure FK.LatticeConfiguration)
    (hφ : Tendsto (fun n => FK.wiredBoxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n) atTop (𝓝 φ))
    (A : Finset (ℤ × ℤ)) (ξ : SpinSpace q) :
    Tendsto (fun n => (pottsBoxProbabilityMeasure q hq β hβ i n).toMeasure.real (spinCylinder q A ξ))
      atTop (𝓝 (wiredESCylinder q φ.toMeasure i hi A ξ)) := by
  rw [← spinObservationEvent_subtype]
  exact tendsto_pottsBox_observed q hq β hβ i (fun a : ↥A => a.val) (fun a : ↥A => ξ a.val)
    (wired_partitionExpectation_tendsto q hq β hβ φ hφ (Option.map Subtype.val) _)
    (fun n hn hv => potts_ghost_cylinder_eq_partitionExpectation q hq β hβ i hi n hn _ hv _)

end
end PottsDiscontinuity.Potts
