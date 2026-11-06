module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnGeometryKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PatchPowerDoubling
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsRegularity
import Mathlib.Tactic

/-! # Classicality and positivity of the canonical reflected return-time solution -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set MeasureTheory SectionTwo Evolution TheoremA

/-- Reflection preserves the smooth autonomous coefficient class. -/
def returnReflectedCoefficient {lam Lam } (A : SmoothAutonomous lam Lam) :
    SmoothAutonomous lam Lam :=
  ⟨reflectedAutonomous A.a, reflectedAutonomous_smooth A, reflectedAutonomous_bounds A⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
