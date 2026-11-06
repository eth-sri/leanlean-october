module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumPower
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumFinite
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GeometricCoreCoverSeries
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! # Real representatives of the actual positive Green density -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped ENNReal

/- A finite measure's positive density is finite almost everywhere. -/
theorem position_density_real {X : Type*} [MeasurableSpace X]
    (m mu : Measure X) [IsFiniteMeasure mu] (F : X → ℝ≥0∞) (hF : Measurable F)
    (hd : m.withDensity F = mu) (q : ℝ) :
    Measurable (fun x => (F x).toReal) ∧ (∀ x, 0 ≤ (F x).toReal) ∧
      mu = m.withDensity (fun x => ENNReal.ofReal (F x).toReal) ∧
      (∫⁻ x, ‖(F x).toReal‖ₑ ^ q ∂m) = ∫⁻ x, F x ^ q ∂m := by
  have hf : ∀ᵐ x ∂m, F x ≠ ⊤ := by
      have hi : (∫⁻ x, F x ∂m) ≠ ⊤ := by
        have he : (m.withDensity F) univ = ∫⁻ x, F x ∂m := by
          rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
        rw [← he, hd]
        exact measure_ne_top _ _
      exact (ae_lt_top hF hi).mono (fun _ h => h.ne)

    /- The real representative has exactly the original positive density and power integral. -/
  refine ⟨hF.ennreal_toReal, fun _ => ENNReal.toReal_nonneg, ?_, ?_⟩
  · rw [← hd]
    apply withDensity_congr_ae
    exact hf.mono (fun _ h => (ENNReal.ofReal_toReal h).symm)
  · apply lintegral_congr_ae
    filter_upwards [hf] with x hx
    rw [Real.enorm_toReal hx]

/- The actual active mixture has a real density with precisely the source power bound. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
