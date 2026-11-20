module

public import NearlyMinimax.HighMarginalScoreEnergy
public import NearlyMinimax.HighMarginalScoreCenter


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
    (dependent : J → J → Prop) (ρ : ℝ) {activation : E → ℝ} (ham : Measurable activation) :
    Measurable (fun z : ℝ × HistoryMarked dependent E =>
      historyMarkedDensity ρ z.1 activation z.2) := by
  apply measurable_uncurry_of_continuous_of_measurable
    (u := fun t ω => historyMarkedDensity ρ t activation ω)
  · intro ω
    exact continuous_iff_continuousAt.mpr (fun t =>
      (historyMarkedDensity_hasDerivAt ρ t activation ω).continuousAt)
  · solve_by_elim [historyMarkedDensity_measurable]

section
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (n : ℕ) (a v η : ℝ) {p F : Ω → Covariate d → ℝ}
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
include hF hp

theorem highRawSampleLikelihood_time_measurable :
    Measurable (fun z : ℝ × (Ω × (IndexedSample d n)) =>
      highRawSampleLikelihood a (v-η^2*z.1) (p z.2.1) (F z.2.1) z.2.2) := by
  fun_prop [highRawSampleLikelihood]

theorem highRawSampleVarianceDerivative_time_measurable :
    Measurable (fun z : ℝ × (Ω × (IndexedSample d n)) =>
      highRawSampleVarianceDerivative a (v-η^2*z.1) (p z.2.1) (F z.2.1) z.2.2) := by
  fun_prop [highRawSampleVarianceDerivative]

end

variable {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] {d : ℕ} {dependent : J → J → Prop}
    [Std.Symm dependent] (π : Measure E) [SFinite π] {activation : E → ℝ} (ham : Measurable activation)
    (n : ℕ) (a v η : ℝ) {p F : HistoryMarked dependent E → Covariate d → ℝ}
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
include hF ham hp

theorem highAppendLikelihoodAction_time_measurable (j : J) :
    Measurable (fun z : ℝ × (HistoryMarked dependent E × (IndexedSample d n)) =>
      highAppendLikelihoodAction π activation a (v-η^2*z.1) p F j z.2.1 z.2.2) := by
  exact ((ham.comp measurable_snd).mul ((highRawSampleLikelihood_time_measurable n a v η hp hF).comp ((measurable_fst.comp measurable_fst).prodMk (((historyMarkedAppend_measurable j).comp ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)).prodMk (measurable_snd.comp (measurable_snd.comp measurable_fst)))))).stronglyMeasurable.integral_prod_right'.measurable

theorem highHistoryLikelihoodDerivative_time_measurable :
    Measurable (fun z : ℝ × (HistoryMarked dependent E × (IndexedSample d n)) =>
      highHistoryLikelihoodDerivative π activation a (v-η^2*z.1) η p F z.2.1 z.2.2) := (Finset.measurable_sum _ (fun j _ =>
    highAppendLikelihoodAction_time_measurable π ham n a v η hp hF j)).sub
      ((highRawSampleVarianceDerivative_time_measurable n a v η hp hF).const_mul (η^2))

end NearlyMinimax
