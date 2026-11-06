module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.IntegratedVelocity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxConcentrationAveraging

/-! # Averaging the velocity-band comparison over the later time window -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set

/-- The later window has length `t`; its occupation is bounded by occupation through `3t`. -/
theorem velocity_return_time_average {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) (z : Z) (r t C : ℝ)
    (ht : 0 < t) (hC : 0 ≤ C)
    (hcomp : ∀ s ∈ Ioc (2 * t) (3 * t),
      velocityBandAction E r t z ≤ C * velocityBandAction E r s z) :
    t * velocityBandAction E r t z ≤
      C * ∫ s in Ioc 0 (3 * t), velocityBandAction E r s z := by
  let f := fun s => velocityBandAction E r s z
  have hi : IntegrableOn _ (Ioc 0 (3 * t)) :=
    velocityBandAction_integrable A E hE r _ z
  have hs : Ioc (2 * t) _ ⊆ Ioc 0 (3 * t) :=
    fun s hs => ⟨by grind, hs.2⟩
  have hsmall := hi.mono_set hs
  have hmono := setIntegral_mono_on
    (integrableOn_const (C := f t) (by simp))
    (hsmall.const_mul C) measurableSet_Ioc hcomp
  have hvol : volume.real (Ioc (2 * t) (3 * t)) = t := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [setIntegral_const, hvol, integral_const_mul] at hmono
  have hnonneg : ∀ s, 0 ≤ velocityBandAction E r s z := fun s => by
    rw [velocityBandAction_eq_probability A E hE]
    positivity
  exact hmono.trans (mul_le_mul_of_nonneg_left
    (setIntegral_mono_set hi (Filter.Eventually.of_forall hnonneg)
      (Filter.Eventually.of_forall hs)) hC)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
