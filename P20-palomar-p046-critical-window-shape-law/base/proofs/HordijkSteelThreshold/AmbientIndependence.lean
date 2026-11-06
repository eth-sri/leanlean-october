module

public import proofs.HordijkSteelThreshold.AmbientOpen
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer

abbrev AmbientCoord (n : Nat) := Molecule n × Reaction n

/-- The one-coordinate law underlying the set-Bernoulli catalysis sample. -/
noncomputable def ambientCoordLaw (p : I) : Measure Prop :=
  toNNReal p • Measure.dirac True + toNNReal (σ p) • Measure.dirac False

noncomputable instance ambientCoordLaw_isProbability (p : I) :
    IsProbabilityMeasure (ambientCoordLaw p) := by
  constructor
  simp [ambientCoordLaw]

/-- The uncurried product presentation of uniform catalysis coordinates. -/
noncomputable def ambientPiMeasure (n : Nat) (lambda : ℝ) :
    Measure (AmbientCoord n → Prop) :=
  Measure.infinitePi (fun _ => ambientCoordLaw (RAF.Concrete.catalysisP n lambda))

noncomputable instance ambientPiMeasure_isProbability (n : Nat) (lambda : ℝ) :
    IsProbabilityMeasure (ambientPiMeasure n lambda) := by
  unfold ambientPiMeasure
  infer_instance

theorem ambientCoordinate_iIndep (n : Nat) (lambda : ℝ) :
    iIndepFun (fun z (ω : AmbientCoord n → Prop) => ω z)
      (ambientPiMeasure n lambda) := by
  unfold ambientPiMeasure
  exact iIndepFun_infinitePi (fun _ => measurable_id)

end HordijkSteelThreshold
