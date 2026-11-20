module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationAllTimeKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapNorm
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FarVelocityDensityDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitCone
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.Tactic

/-! # Canonical active Green kernels and their actual jointly measurable densities -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Classical

/-- The literal coordinate product makes physical spacetime second countable. -/
instance positionPoint_secondCountableTopology : SecondCountableTopology Point :=
  (HypoellipticAleksandrov.KineticPoint.homeomorphProd 1).secondCountableTopology

/-- The pushforward predecessor supplies absolute continuity of every actual active pole. -/
theorem enlargedActiveGreenKernel_absolutelyContinuous (hpush : PushforwardStatement)
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) :
    enlargedActiveGreenKernel A c e ≪ (volume : Measure Point) := by
  by_cases he : e.velocity 0 ∈ c.active
  · obtain ⟨C, _, hd⟩ := (hpush lam Lam A.positive A.ordered).2 (5 / 4) (by norm_num)
    obtain ⟨G, _, _, hG, _, _⟩ := hd A c e he
    rw [enlargedActiveGreenKernel_apply A c e he, hG]
    exact (withDensity_absolutelyContinuous _ _).trans
      Measure.restrict_le_self.absolutelyContinuous
  · change (if hp : e.velocity 0 ∈ c.active then
      stripGreen A c.activeInterval ⊤ (densityClockPole c e hp)
      else 0) ≪ volume
    rw [dite_eq_right he]
    intro B _
    rfl

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock)
include lam Lam A c

/-- The actual joint extended density of the all-time active Green kernel. -/
def positionActiveDensity : Point → Point → ℝ≥0∞ := by
  letI := density_volume_sigmaFinite
  exact positionKernelDensity (enlargedActiveGreenKernel A c) volume

/-- The active density is jointly measurable in the physical starting and observed points. -/
theorem measurable_positionActiveDensity :
    Measurable (fun p : Point × Point =>
      positionActiveDensity A c p.1 p.2) := by
  have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
  exact measurable_positionKernelDensity
    (enlargedActiveGreenKernel A c) (volume : Measure Point)

end

/-- The jointly measurable density represents the same canonical active kernel. -/
theorem withDensity_positionActiveDensity (hpush : PushforwardStatement)
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) :
    volume.withDensity (positionActiveDensity A c e) =
      enlargedActiveGreenKernel A c e := by
  have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
  exact withDensity_positionKernelDensity
    (enlargedActiveGreenKernel A c) (volume : Measure Point) e
    (enlargedActiveGreenKernel_absolutelyContinuous hpush A c e)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
