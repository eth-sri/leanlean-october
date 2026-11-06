module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.IntegratedVelocityBand
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Time integration of actual velocity-band transition probabilities -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory Filter
open SectionTwo
open scoped ENNReal

/-- Velocity band on the native terminal state. -/
def velocityNativeBand (r : ℝ) : Set (EvolutionAmbientState 1) := {w | |w.1 0| ≤ 3 * r}

/-- Native terminal velocity bands are measurable. -/
theorem velocityNativeBand_measurable (r : ℝ) : MeasurableSet (velocityNativeBand r) := measurableSet_le
    (continuous_abs.measurable.comp ((measurable_pi_apply 0).comp measurable_fst))
    measurable_const

/-- Actual transition probability of the velocity band, extended to negative times by time zero. -/
def velocityBandProbability (E : FullSpaceEvolution) (r : ℝ) (z : Z) (t : ℝ) : ℝ≥0∞ :=
  E.2.master (wholeQuery (Real.toNNReal t) z) (velocityNativeBand r)

variable (E : FullSpaceEvolution) {T : ℝ} (hT : 0 < T) (r : ℝ) (z : Z)

/-- The query curve for the actual transition kernel is measurable. -/
theorem velocityWholeQuery_measurable  :
    Measurable (fun t : ℝ => wholeQuery (Real.toNNReal t) z) := by
  unfold wholeQuery wholeSpaceQuery
  fun_prop

/-- Actual band probabilities depend measurably on elapsed time. -/
theorem velocityBandProbability_measurable  :
    Measurable (velocityBandProbability E r z) :=
  (E.2.master.measurable_coe (velocityNativeBand_measurable r)).comp
    (velocityWholeQuery_measurable z)

/-- Band transition probabilities are bounded by one. -/
theorem velocityBandProbability_le_one  (t : ℝ) :
    velocityBandProbability E r z t ≤ 1 :=
  (measure_mono (subset_univ _)).trans (E.2.mass_le_one _)

/-- Green band mass is the unnormalized elapsed-time integral of transition probabilities. -/
theorem velocityGreenRaw_band_eq_lintegral  :
    velocityGreenRaw E T hT z (velocityRawBand r) =
      ∫⁻ t in Ioo 0 T, velocityBandProbability E r z t := by
  let B := velocityElapsedRaw (T := T) ⁻¹' velocityRawBand r
  have hB : MeasurableSet B :=
    (velocityElapsedRaw_measurable T) (velocityRawBand_measurable r)
  rw [velocityGreenRaw, Measure.map_apply (velocityElapsedRaw_measurable T)
    (velocityRawBand_measurable r), ← lintegral_indicator_one hB]
  rw [velocityGreen, greenMeasure_spec E.2 0 _ _
    _ _ (measurable_one.indicator hB)]
  have he (t : ElapsedTime (ENNReal.ofReal T)) :
      elapsedQuery 0 (velocityInitialState z) t = wholeQuery (Real.toNNReal t.1) z := by
    apply Subtype.ext
    simp only [elapsedQuery, velocityInitialState, wholeQuery, wholeSpaceQuery,
      Real.coe_toNNReal _ t.2.1.le, zero_add]
  have hh : (∫⁻ t : ElapsedTime _,
      ∫⁻ w, B.indicator 1 (t, w) ∂E.2.master (elapsedQuery 0 (velocityInitialState z) t)
        ∂elapsedVolume _) =
      ∫⁻ t : ElapsedTime _, velocityBandProbability E r z t
        ∂elapsedVolume (ENNReal.ofReal T) := by
    apply lintegral_congr
    intro t
    rw [he]
    exact lintegral_indicator_one (velocityNativeBand_measurable r)
  have hi := lintegral_subtype_comap (μ := volume)
    (measurableSet_elapsedTime (ENNReal.ofReal T)) (velocityBandProbability E r z)
  aesop

/-- Real band probabilities are integrable on every finite time interval. -/
theorem velocityBandProbability_toReal_integrable  (T : ℝ) :
    Integrable (fun t => (velocityBandProbability E r z t).toReal)
      (volume.restrict (Ioc 0 T)) := by
  apply Integrable.mono' (integrable_const (1))
    (velocityBandProbability_measurable E r z).ennreal_toReal.aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top
      (velocityBandProbability_le_one E r z t)

/-- Ordinary real time integration is the real value of Green band mass. -/
theorem velocity_band_integral_eq_green  :
    (∫ t in Ioc 0 T, (velocityBandProbability E r z t).toReal) =
      (velocityGreenRaw E T hT z (velocityRawBand r)).toReal := by
  rw [integral_Ioc_eq_integral_Ioo, integral_toReal
    (velocityBandProbability_measurable E r z).aemeasurable]
  · rw [velocityGreenRaw_band_eq_lintegral]
  · exact Eventually.of_forall fun t =>
      (velocityBandProbability_le_one E r z t).trans_lt ENNReal.one_lt_top

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
