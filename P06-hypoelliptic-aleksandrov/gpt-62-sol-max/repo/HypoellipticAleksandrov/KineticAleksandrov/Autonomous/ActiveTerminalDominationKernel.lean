module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlabKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionTerminalFamily
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlabKernel

/-! # The measurable kernel of the canonical enlarged terminal family -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open scoped Classical

/-- Kernel packaging of the already defined actual terminal family. -/
def enlargedTerminalFamilyKernel
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) : Kernel Point Point :=
  ⟨enlargedActiveTerminalFamily A c J b,
    _root_.HypoellipticAleksandrov.KineticAleksandrov.Autonomous.entranceSlabTerminalFamily_measurable A c J b⟩

/-- The actual terminal kernel is uniformly finite with bound one. -/
instance enlargedTerminalFamilyKernel_isFiniteKernel
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) :
    IsFiniteKernel (enlargedTerminalFamilyKernel A c J b) :=
  ⟨1, ENNReal.one_lt_top,
    enlarged_terminal_family_mass_le_one A c J b⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
