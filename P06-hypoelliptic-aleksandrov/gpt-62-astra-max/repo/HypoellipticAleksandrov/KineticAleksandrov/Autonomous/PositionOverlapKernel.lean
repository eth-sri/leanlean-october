module

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

/-- The active Green kernel agrees with the canonical Green at every valid starting velocity. -/
theorem enlargedActiveGreenKernel_apply
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    enlargedActiveGreenKernel hlam hLam A c e =
      stripGreen hlam hLam A c.activeInterval ⊤ (densityClockPole c e he) := by
  change (if hp : e.velocity 0 ∈ c.active then
    stripGreen hlam hLam A c.activeInterval ⊤ (densityClockPole c e hp) else 0) = _
  rw [dite_eq_left he]

/-- Uniform quadratic mass makes the all-time physical active family a finite kernel. -/
instance enlargedActiveGreenKernel_isFiniteKernel
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) :
    IsFiniteKernel (enlargedActiveGreenKernel hlam hLam A c) := by
  refine ⟨ENNReal.ofReal ((3 * c.r / 2) ^ 2 / (2 * lam)), ENNReal.ofReal_lt_top, ?_⟩
  intro e
  by_cases he : e.velocity 0 ∈ c.active
  · rw [enlargedActiveGreenKernel_apply hlam hLam A c e he]
    apply (stripGreen_quadratic_mass hlam hLam A c.activeInterval ⊤ _).trans
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_div_iff_of_pos_right (by linarith : 0 < 2 * lam)).2
    change (e.velocity 0 - (c.vbar - 3 * c.r / 4)) *
      (c.vbar + 3 * c.r / 4 - e.velocity 0) ≤ (3 * c.r / 2) ^ 2
    nlinarith only [sq_nonneg (e.velocity 0 - c.vbar), sq_nonneg c.r]
  · change (if hp : e.velocity 0 ∈ c.active then
      stripGreen hlam hLam A c.activeInterval ⊤ (densityClockPole c e hp)
      else 0) univ ≤ _
    rw [dite_eq_right he]
    exact zero_le

variable (hpush : PushforwardStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)

include hpush in
/-- The pushforward predecessor supplies absolute continuity of every actual active pole. -/
theorem enlargedActiveGreenKernel_absolutelyContinuous :
    enlargedActiveGreenKernel hlam hLam A c e ≪ (volume : Measure Point) := by
  by_cases he : e.velocity 0 ∈ c.active
  · obtain ⟨C, _, hd⟩ := (hpush lam Lam hlam hLam).2 (5 / 4) (by norm_num)
    obtain ⟨G, _, _, hG, _, _⟩ := hd A c e he
    rw [enlargedActiveGreenKernel_apply hlam hLam A c e he, hG]
    exact (withDensity_absolutelyContinuous _ _).trans
      Measure.restrict_le_self.absolutelyContinuous
  · change (if hp : e.velocity 0 ∈ c.active then
      stripGreen hlam hLam A c.activeInterval ⊤ (densityClockPole c e hp)
      else 0) ≪ volume
    aesop

include hlam hLam A c in
/-- The actual joint extended density of the all-time active Green kernel. -/
def positionActiveDensity : Point → Point → ℝ≥0∞ := by
  letI := density_volume_sigmaFinite
  exact positionKernelDensity (enlargedActiveGreenKernel hlam hLam A c) volume

/-- The active density is jointly measurable in the physical starting and observed points. -/
theorem measurable_positionActiveDensity :
    Measurable (fun p : Point × Point =>
      positionActiveDensity hlam hLam A c p.1 p.2) := by
  have  := density_volume_sigmaFinite
  apply measurable_positionKernelDensity

include hpush in
/-- The jointly measurable density represents the same canonical active kernel. -/
theorem withDensity_positionActiveDensity :
    volume.withDensity (positionActiveDensity hlam hLam A c e) =
      enlargedActiveGreenKernel hlam hLam A c e := by
  have  := density_volume_sigmaFinite
  exact withDensity_positionKernelDensity
    (enlargedActiveGreenKernel hlam hLam A c) volume e
    (enlargedActiveGreenKernel_absolutelyContinuous hpush hlam hLam A c e)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
