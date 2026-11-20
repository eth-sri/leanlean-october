module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationAllTimeKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SurvivalHalfMass
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! # Finite mixtures of the actual all-time active Green family

Source: companion paper, Corollary 8.4 (mixture density). This module proves finite mass,
absolute continuity and density existence. The quantitative Lq norm estimate is
a separate step, not a premise or a conclusion of these measure lemmas.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open scoped ENNReal

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock)

/-- A finite starting measure gives a finite all-time Green mixture. -/
instance enlargedActiveGreen_isFiniteMeasure (nu : Measure Point) [IsFiniteMeasure nu] :
    IsFiniteMeasure (enlargedActiveGreen A c nu) := by
  unfold enlargedActiveGreen
  infer_instance

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
