module

public import proofs.HordijkSteelThreshold.GatewayProbability
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer

abbrev AmbientCoord (n : Nat) := Molecule n × Reaction n

variable (p : I)

/-- The one-coordinate law underlying the set-Bernoulli catalysis sample. -/
noncomputable def ambientCoordLaw  : Measure Prop :=
  toNNReal p • Measure.dirac True + toNNReal (σ p) • Measure.dirac False

noncomputable instance ambientCoordLaw_isProbability  :
    IsProbabilityMeasure (ambientCoordLaw p) := by
  constructor
  simp [ambientCoordLaw]


variable (n : Nat) (lambda : ℝ)

/-- The uncurried product presentation of uniform catalysis coordinates. -/
noncomputable def ambientPiMeasure  :
    Measure (AmbientCoord n → Prop) :=
  Measure.infinitePi $ fun _ => ambientCoordLaw $ RAF.Concrete.catalysisP n lambda

noncomputable instance ambientPiMeasure_isProbability  :
    IsProbabilityMeasure (ambientPiMeasure n lambda) := by
  unfold ambientPiMeasure
  infer_instance

theorem ambientCoordinate_iIndep  :
    iIndepFun (fun z (ω : AmbientCoord n → Prop) => ω z)
      (ambientPiMeasure n lambda) := by
  exact iIndepFun_infinitePi $ fun _ => measurable_id

end HordijkSteelThreshold
