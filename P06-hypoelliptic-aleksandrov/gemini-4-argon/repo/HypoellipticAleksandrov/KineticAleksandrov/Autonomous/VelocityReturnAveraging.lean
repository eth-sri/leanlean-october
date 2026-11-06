module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.IntegratedVelocity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxConcentrationAveraging
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomyPhysicalSemigroup
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.IntegratedVelocityTime
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.IntegratedVelocityBand
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Averaging the velocity-band comparison over the later time window -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set
open SectionTwo
open Filter
open scoped ENNReal

/- The later window has length `t`; its occupation is bounded by occupation through `3t`. -/
theorem velocity_return_time_average {lam Lam } (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) (z ) (r t C : ℝ)
    (ht : 0 < t) (hC : 0 ≤ C)
    (hcomp : ∀ s ∈ Ioc (2 * t) (3 * t),
      velocityBandAction E r t z ≤ C * velocityBandAction E r s z) :
    t * velocityBandAction E r t z ≤
      C * ∫ s in Ioc 0 (3 * t), velocityBandAction E r s z := by
  let f := fun s => velocityBandAction E r s z
  have hi : IntegrableOn (fun s => velocityBandAction E r s z) (Ioc 0 (3 * t)) := by
    let T := (3 * t)
    have he :=
      funext fun t => velocityBandAction_eq_probability A E hE r t z
    rw [he]
    apply Integrable.mono' (integrable_const (1 : ℝ))
      (velocityBandProbability_measurable E r z).ennreal_toReal.aestronglyMeasurable
    exact Eventually.of_forall fun t => by
      rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
      simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top
        (velocityBandProbability_le_one E r z t)
  have hs : Ioc (2 * t) (3 * t) ⊆ Ioc 0 (3 * t) :=
    fun s hs => ⟨by linarith [hs.1], hs.2⟩
  have hsmall := hi.mono_set hs
  have hmono := setIntegral_mono_on
    (integrableOn_const (C := f t) (by simp : volume (Ioc (2 * t) (3 * t)) ≠ ⊤))
    (hsmall.const_mul C) measurableSet_Ioc hcomp
  have hvol : volume.real (Ioc (2 * t) (3 * t)) = t := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [setIntegral_const, hvol, smul_eq_mul, integral_const_mul] at hmono
  have hnonneg : ∀ s, 0 ≤ velocityBandAction E r s z := fun s => by
    rw [velocityBandAction_eq_probability A E hE]
    exact ENNReal.toReal_nonneg
  exact hmono.trans (mul_le_mul_of_nonneg_left
    (setIntegral_mono_set hi (Filter.Eventually.of_forall hnonneg)
      (Filter.Eventually.of_forall hs)) hC)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
