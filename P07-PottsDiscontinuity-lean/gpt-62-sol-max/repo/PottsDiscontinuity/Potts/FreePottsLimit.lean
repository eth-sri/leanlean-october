module

public import PottsDiscontinuity.Potts.FreeSpinObservations
public import PottsDiscontinuity.Potts.ESCylinderLaw
public import PottsDiscontinuity.Potts.PottsLimitConstruction

/-! Free Potts box limits and their Edwards–Sokal colouring identification. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section

theorem free_potts_cylinder_tendsto (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (φ : ProbabilityMeasure FK.LatticeConfiguration)
    (hφ : Tendsto (fun n => FK.boxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n) atTop (𝓝 φ))
    (A : Finset (ℤ × ℤ)) (ξ : SpinSpace q) :
    Tendsto (fun n => (pottsBoxProbabilityMeasure q hq β hβ 0 n).toMeasure.real (spinCylinder q A ξ))
      atTop (𝓝 (freeESCylinder q φ.toMeasure A ξ)) := by
  rw [← spinObservationEvent_subtype]
  exact free_spin_observation_tendsto q hq β hβ φ hφ Subtype.val (fun a : ↥A => ξ a.val)

end
end PottsDiscontinuity.Potts
