module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionTerminalFamily
import Batteries.Tactic.Alias
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlabKernel



/-! # The measurable kernel of the canonical enlarged terminal family -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory ProbabilityTheory
open scoped Classical

variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ)

/-- The actual terminal family is measurable even on its zero-duration face. -/
alias enlarged_terminal_family_measurable := _root_.HypoellipticAleksandrov.KineticAleksandrov.Autonomous.entranceSlabTerminalFamily_measurable


/-- Kernel packaging of the already defined actual terminal family. -/
def enlargedTerminalFamilyKernel
     : Kernel Point Point :=
  ⟨_,
    enlarged_terminal_family_measurable hH hLE hlam hLam A c J b⟩

/-- The actual terminal kernel is uniformly finite with bound one. -/
instance enlargedTerminalFamilyKernel_isFiniteKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) :
    IsFiniteKernel (enlargedTerminalFamilyKernel hH hLE hlam hLam A c J b) :=
  ⟨1, ENNReal.one_lt_top,
    enlarged_terminal_family_mass_le_one hH hLE hlam hLam A c J b⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
