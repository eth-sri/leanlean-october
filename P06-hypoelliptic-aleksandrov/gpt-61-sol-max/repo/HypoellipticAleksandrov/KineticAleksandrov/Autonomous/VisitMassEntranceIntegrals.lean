module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassQuadratic
import Mathlib.Tactic
import Aesop



/-! # The quadratic lower bound integrated over actual entrance pieces -/

 public section
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
    · aesop
    · exact (ae_restrict_mem
        (measurableSet_visitBoundary s T (visitEntranceInterval c) J)).mono
          (fun _ hp => frontier_subset_closure hp.2.2.1)
  | succ n =>
    exact (ae_restrict_mem
      (measurableSet_visitBoundary s T (visitEntranceInterval c) J)).mono
        (fun _ hp => frontier_subset_closure hp.2.2.1)

variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (P : Point) (n : ℕ)

/-- The physical quadratic is integrable against every actual finite entrance piece. -/
theorem visitQuadratic_integrable_entrance
     :
    Integrable (fun p => visitQuadratic c (p.velocity 0))
      (visitEntrancePiece hH hLE hlam hLam A c J s T P n) := by

  apply Integrable.mono' (integrable_const (9 * c.r ^ 2 / 16)) ((visitQuadratic_smooth c).continuous.comp ((continuous_apply 0).comp continuous_velocity)).measurable.aestronglyMeasurable
  filter_upwards [visitGamma_ae_closedEntrance P c J s T
    _
    _ n] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact visitQuadratic_le c _
  · exact (by positivity : 0 ≤ 5 * c.r ^ 2 / 16).trans
      (visitQuadratic_entrance_lower c hp)

/-- The exact five-sixteenths lower bound survives integration, with the initial atom included. -/
theorem visitQuadratic_entrance_integral_lower
     :
    5 * c.r ^ 2 / 16 * (visitEntrancePiece hH hLE hlam hLam A c J s T P n univ).toReal ≤
      ∫ p, visitQuadratic c (p.velocity 0)
        ∂visitEntrancePiece hH hLE hlam hLam A c J s T P n := by

  have hb := integral_mono_ae (integrable_const (5 * c.r ^ 2 / 16)) (visitQuadratic_integrable_entrance hH hLE hlam hLam A c J s T P n) (by
    filter_upwards [visitGamma_ae_closedEntrance P c J s T
      _
      _ n] with p hp
    exact visitQuadratic_entrance_lower c hp)
  simpa only [integral_const, smul_eq_mul, Measure.real, mul_comm] using hb

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
