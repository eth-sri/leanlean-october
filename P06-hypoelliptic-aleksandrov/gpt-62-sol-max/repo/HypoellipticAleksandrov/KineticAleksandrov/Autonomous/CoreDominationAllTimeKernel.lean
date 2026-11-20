module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisits
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassQuadratic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassInfinite
import Mathlib.Tactic

/-! # The actual physical all-time active-strip Green kernel for core domination -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock)
include lam Lam A c

/-- At an active velocity the global kernel is the all-time strip Green measure. -/
theorem enlargedActiveGreenKernel_apply (p : Point) (hp : p.velocity 0 ∈ c.active) :
    enlargedActiveGreenKernel A c p = stripGreen A c.activeInterval ⊤ (densityClockPole c p hp) :=
  visitExtendKernel_apply_mem hp

/-- Its physical occupation mass has the exact quadratic upper bound independent of pole time. -/
theorem enlargedActiveGreenKernel_mass_le (p : Point) :
    enlargedActiveGreenKernel A c p univ ≤
      ENNReal.ofReal (9 * c.r ^ 2 / (32 * lam)) := by
  classical
  change (if hp : p.velocity 0 ∈ c.active then
    stripGreen A (visitActiveInterval c) ⊤ (densityClockPole c p hp)
      else 0) univ ≤ _
  split
  · rename_i hp
    apply (stripGreen_quadratic_mass A (visitActiveInterval c) ⊤
      (densityClockPole c p hp)).trans
    apply ENNReal.ofReal_le_ofReal
    change visitQuadratic c (p.velocity 0) / (2 * lam) ≤ 9 * c.r ^ 2 / (32 * lam)
    calc
      _ ≤ (9 * c.r ^ 2 / 16) / (2 * lam) :=
        div_le_div_of_nonneg_right (visitQuadratic_le c _) (by have := A.positive; positivity)
      _ = _ := by field_simp; ring
  · exact zero_le

end

/-- The actual all-time active-strip kernel is uniformly finite. -/
instance enlargedActiveGreenKernel_isFiniteKernel
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (c : Clock) :
    IsFiniteKernel (enlargedActiveGreenKernel A c) :=
  ⟨ENNReal.ofReal (9 * c.r ^ 2 / (32 * lam)), ENNReal.ofReal_lt_top,
    enlargedActiveGreenKernel_mass_le A c⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
