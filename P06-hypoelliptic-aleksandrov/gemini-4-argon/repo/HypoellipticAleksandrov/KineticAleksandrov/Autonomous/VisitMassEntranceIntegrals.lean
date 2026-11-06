module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassQuadratic
import Mathlib.Tactic

/-! # The quadratic lower bound integrated over actual entrance pieces -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open scoped Classical

/- Every entrance, including the possible initial atom, lies in the closed entrance interval. -/
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

/- The physical quadratic is integrable against every actual finite entrance piece. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
