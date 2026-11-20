module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassQuadratic
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreStartBandVisits

/-! # The quadratic lower bound integrated over actual entrance pieces -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open scoped Classical

/-- Every entrance, including the possible initial atom, lies in the closed entrance interval. -/
theorem visitGamma_ae_closedEntrance (P : Point) (c : Clock) (J : Interval) (s T : ℝ)
    (exitActive exitWaiting : Kernel Point Point) (n : ℕ) :
    ∀ᵐ p ∂visitGamma P (visitEntranceInterval c)
      (visitBoundary s T (visitEntranceInterval c) J)
      (visitBoundary s T (visitActiveInterval c) J) exitActive exitWaiting n,
      p.velocity 0 ∈ closure c.entrance := by
  cases n with
  | zero =>
    change ∀ᵐ p ∂visitInitial P (visitEntranceInterval c)
      (visitBoundary s T (visitEntranceInterval c) J) exitWaiting,
      p.velocity 0 ∈ closure c.entrance
    unfold visitInitial
    split
    · rename_i hi
      exact (ae_dirac_iff (isClosed_closure.measurableSet.preimage
        ((continuous_apply 0).comp continuous_velocity).measurable)).mpr hi
    · exact (ae_restrict_mem
        (measurableSet_visitBoundary s T (visitEntranceInterval c) J)).mono
          (fun _ hp => frontier_subset_closure hp.2.2.1)
  | succ n =>
    exact (ae_restrict_mem
      (measurableSet_visitBoundary s T (visitEntranceInterval c) J)).mono
        (fun _ hp => frontier_subset_closure hp.2.2.1)

section
variable (c : Clock) (mu : Measure Point)

/-- The nonnegative source quadratic is bounded on the closed active interval. -/
theorem visitQuadratic_integrable_of_active_support
    [IsFiniteMeasure mu] (hm : ∀ᵐ p ∂mu, p.velocity 0 ∈ closure c.active) :
    Integrable (fun p => visitQuadratic c (p.velocity 0)) mu := by
  refine (integrable_const (9 * c.r ^ 2 / 16)).mono' (((visitQuadratic_smooth c).continuous.comp
    ((continuous_apply 0).comp continuous_velocity)).measurable.aestronglyMeasurable) ?_
  filter_upwards [hm] with p hp
  simpa only [Real.norm_eq_abs, abs_of_nonneg (visitQuadratic_nonneg c hp)] using
    visitQuadratic_le c (p.velocity 0)

/-- Integrating the lower bound on the closed entrance interval. -/
theorem visitQuadratic_integral_lower_of_entrance_support
    [IsFiniteMeasure mu] (hm : ∀ᵐ p ∂mu, p.velocity 0 ∈ closure c.entrance) :
    5 * c.r ^ 2 / 16 * (mu univ).toReal ≤ ∫ p, visitQuadratic c (p.velocity 0) ∂mu := by
  have hi := visitQuadratic_integrable_of_active_support c mu
    (hm.mono fun _ hp => subset_closure (_root_.HypoellipticAleksandrov.KineticAleksandrov.Autonomous.enlargedEntrance_subset_active c hp))
  simpa only [integral_const, smul_eq_mul, Measure.real, mul_comm] using
    integral_mono_ae (integrable_const (5 * c.r ^ 2 / 16)) hi
      (hm.mono fun _ hp => visitQuadratic_entrance_lower c hp)

end

/-- The exact five-sixteenths lower bound survives integration, with the initial atom included. -/
theorem visitQuadratic_entrance_integral_lower
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (n : ℕ) :
    5 * c.r ^ 2 / 16 * (visitEntrancePiece A c J s T P n univ).toReal ≤
      ∫ p, visitQuadratic c (p.velocity 0)
        ∂visitEntrancePiece A c J s T P n := 
  visitQuadratic_integral_lower_of_entrance_support c _
    (visitGamma_ae_closedEntrance P c J s T _ _ n)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
