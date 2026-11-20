module

public import NearlyMinimax.HighMarginalScoreEnergy
public import NearlyMinimax.HighMarginalScoreDerivative


@[expose] public section

/-! Genuine joint time measurability of source priors and likelihood scores. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

theorem historyMarkedDensity_joint_measurable {E : Type*} [MeasurableSpace E]
    (dependent : J → J → Prop) (ρ : ℝ) (activation : E → ℝ) (ham : Measurable activation) :
    Measurable (fun z : ℝ × HistoryMarked dependent E =>
      historyMarkedDensity dependent ρ z.1 activation z.2) := by
  apply measurable_uncurry_of_continuous_of_measurable
    (u := fun (t : ℝ) (ω : HistoryMarked dependent E) => historyMarkedDensity dependent ρ t activation ω)
  · intro ω
    exact continuous_iff_continuousAt.mpr (fun t =>
      (historyMarkedDensity_hasDerivAt dependent ρ t activation ω).continuousAt)
  · exact fun t => historyMarkedDensity_measurable dependent ρ t activation ham

end NearlyMinimax
