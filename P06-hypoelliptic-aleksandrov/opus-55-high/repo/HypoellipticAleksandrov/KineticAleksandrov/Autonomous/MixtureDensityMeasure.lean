module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisits
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SurvivalHalfMass
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.MixtureDensityRadonNikodym

/-! # Finite mixtures of the actual all-time active Green family

Source: companion paper, Corollary 8.4 (mixture density). This module proves finite mass,
absolute continuity and density existence. The quantitative Lq norm estimate is
a separate step, not a premise or a conclusion of these measure lemmas.
-/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open scoped ENNReal

variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)

/-- The all-time active Green kernel is uniformly finite by the quadratic occupation bound. -/
theorem mixtureActiveGreenKernel_isFiniteKernel
     (c : Clock) :
    IsFiniteKernel (enlargedActiveGreenKernel hH hLE hlam hLam A c) := by
  classical
  refine ⟨ENNReal.ofReal (activeHalfMassTime lam c / 2), ENNReal.ofReal_lt_top, ?_⟩
  intro e
  change (if he : e.velocity 0 ∈ c.active then
    stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he)
      else 0) univ ≤ _
  split
  · rename_i he
    exact (stripGreen_quadratic_mass hH hLE hlam hLam A c.activeInterval ⊤
      _).trans
        (ENNReal.ofReal_le_ofReal (active_quadratic_occupation_le hlam c _))
  positivity

/-- A finite starting measure gives a finite all-time Green mixture. -/
theorem enlargedActiveGreen_isFiniteMeasure
     (c : Clock) (nu : Measure Point) [IsFiniteMeasure nu] :
    IsFiniteMeasure (enlargedActiveGreen hH hLE hlam hLam A c nu) := by
  unfold enlargedActiveGreen
  have := mixtureActiveGreenKernel_isFiniteKernel hH hLE hlam hLam A c
  infer_instance

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
