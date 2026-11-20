module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.IntegratedVelocity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxConcentrationAveraging

/-! # Averaging the velocity-band comparison over the later time window -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set

/-- The later window has length `t`; its occupation is bounded by occupation through `3t`. -/
theorem velocity_return_time_average {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) (z : Z) (r t C : ℝ)
    (ht : 0 < t) (hC : 0 ≤ C)
    (hcomp : ∀ s ∈ Ioc (2 * t) (3 * t),
      velocityBandAction E r t z ≤ C * velocityBandAction E r s z) :
    t * velocityBandAction E r t z ≤
      C * ∫ s in Ioc 0 (3 * t), velocityBandAction E r s z :=
  later_window_average ht hC (velocityBandAction_integrable A E hE r (3 * t) z)
    (fun s => by rw [velocityBandAction_eq_probability A E hE]; exact ENNReal.toReal_nonneg)
    hcomp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
