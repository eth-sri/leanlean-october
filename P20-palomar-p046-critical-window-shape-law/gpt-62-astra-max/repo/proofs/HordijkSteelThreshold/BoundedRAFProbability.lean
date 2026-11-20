module

public import proofs.HordijkSteelThreshold.BoundedRAFSeed

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal

theorem ambient_coordinate_probability (n : ℕ) (lambda : ℝ) (z : AmbientCoord n) :
    ambientPiMeasure n lambda {ω | ω z} = (toNNReal (catalysisP n lambda) : ENNReal) := by
  have hm := Measure.infinitePi_map_eval (fun _ : AmbientCoord n =>
    ambientCoordLaw (catalysisP n lambda)) z
  have he := congrArg (fun μ : Measure Prop => μ {True}) hm
  rw [Measure.map_apply (measurable_pi_apply z) (MeasurableSet.singleton True)] at he
  simpa [ambientPiMeasure, ambientCoordLaw] using he

def boundedSeedCatalystEvent (n K : ℕ) : Set (AmbientCoord n → Prop) :=
  {ω | ∃ x : Molecule n, ∃ r : Reaction n,
    molLength x ≤ K ∧ RevSeedReaction (binaryPolymerCRS n 2) r ∧ ω (x,r)}

end HordijkSteelThreshold
