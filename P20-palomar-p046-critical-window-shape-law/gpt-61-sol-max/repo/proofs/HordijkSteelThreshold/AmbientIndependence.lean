
import proofs.HordijkSteelThreshold.GatewayProbability
import Mathlib.Probability.Independence.InfinitePi



namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory unitInterval
open RAF.Polymer

variable (n : Nat)

abbrev AmbientCoord  := Molecule n × Reaction n

/-- The one-coordinate law underlying the set-Bernoulli catalysis sample. -/
noncomputable def ambientCoordLaw (p : I)  :=
  toNNReal p • Measure.dirac True + toNNReal (σ p) • Measure.dirac False

noncomputable instance ambientCoordLaw_isProbability (p : I) :
    IsProbabilityMeasure (ambientCoordLaw p) := by
  constructor
  simp [ambientCoordLaw]

/-- The uncurried product presentation of uniform catalysis coordinates. -/
noncomputable def ambientPiMeasure  (lambda : ℝ) :
    Measure (AmbientCoord n → Prop) :=
  Measure.infinitePi fun _ => ambientCoordLaw (RAF.Concrete.catalysisP n lambda)

theorem probability_prop_eq_of_false (μ ν : Measure Prop)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : μ {False} = ν {False}) : μ = ν := by
  apply Measure.ext_of_singleton
  intro q
  by_cases hq : q
  · 
    have hs : ({True} : Set Prop) = {False}ᶜ := by  simp
    rw [propext (iff_true_intro hq)]
    simp only [hs, prob_compl_eq_one_sub (MeasurableSet.singleton False), h]
  simp_all

end HordijkSteelThreshold
