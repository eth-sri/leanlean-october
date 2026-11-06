module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreen

/-! # Unique characterization of the physical Green measure

The elapsed-time action is literal time integration of the killed kernel. This formulation
keeps every query valid and applies to finite and infinite terminal horizons.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

/-- The physical Green action, stated with positive elapsed times and absolute-time points. -/
def IsStripGreen (H : Interval) (K : MovingFiberKernel (intervalDomain H) (fun _ => 0))
    (T : WithTop ℝ) (e : StripPole H T) (Γ : Measure Point) : Prop :=
  ∀ F : Point → ℝ≥0∞, Measurable F →
    (∫⁻ p, F p ∂Γ) = ∫⁻ τ, ∫⁻ w, F (elapsedPhysicalPoint e.1.time (τ, w))
      ∂K.master (elapsedQuery e.1.time (stripPoleState H T e) τ)
      ∂elapsedVolume (stripHorizon T e.1.time)

/-- The coordinate image of the unique Green measure has the exact Green action. -/
theorem stripGreenOfKernel_spec (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0))
    (T : WithTop ℝ) (e : StripPole H T) :
    IsStripGreen H K T e (stripGreenOfKernel H K T e) := by
  intro F hF
  rw [stripGreenOfKernel, lintegral_map hF (measurable_elapsedPhysicalPoint _ _)]
  have hs := greenMeasure_spec K e.1.time _
    (stripHorizon_pos H T e) (Measure.dirac (stripPoleState H T e))
    (fun q => F (elapsedPhysicalPoint e.1.time q))
    (hF.comp (measurable_elapsedPhysicalPoint _ _))
  refine hs.trans ?_
  simp

/-- The canonical autonomous measure has the literal killed-kernel integration formula. -/
theorem stripGreen_lintegral
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : WithTop ℝ)
    (e : StripPole H T) (F : Point → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p ∂stripGreen hH hLE hlam hLam A H T e) =
      ∫⁻ τ, ∫⁻ w, F (elapsedPhysicalPoint e.1.time (τ, w))
        ∂(stripEvolution hH hLE hlam hLam A H).2.master
          (elapsedQuery e.1.time (stripPoleState H T e) τ)
        ∂elapsedVolume (stripHorizon T e.1.time) :=
  stripGreenOfKernel_spec H _ T e F hF

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
