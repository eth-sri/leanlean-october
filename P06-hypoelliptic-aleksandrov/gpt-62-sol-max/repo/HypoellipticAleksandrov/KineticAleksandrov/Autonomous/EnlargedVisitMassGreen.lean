module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassIntegratedGreen
import Mathlib.Tactic

import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral

/-! # Finite quadratic Green integrals for enlarged-strip entrances -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- On poles after `s`, the enlarged Green kernel agrees with a finite clipped kernel. -/
theorem enlargedVisitGreen_comp_eq_clipped
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (s T : ℝ)
    (mu : Measure Point) (hs : ∀ᵐ p ∂mu, s ≤ p.time) :
    enlargedVisitGreenKernel A H T ∘ₘ mu =
      visitUnionGreenKernel A H (s - 1) T ∘ₘ mu :=
  visitExtendKernel_comp_eq_clipped H s T (finiteUnionGreen A H T)
    (finiteUnionGreen_measurable A H T) mu hs

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval)

/-- Each actual active occupation is finite, although its unrestricted kernel is not uniform. -/
theorem enlargedActivePiece_isFiniteMeasure (s T : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T) (n : ℕ) :
    IsFiniteMeasure (enlargedActivePiece A c J s T P n) := by
  unfold enlargedActivePiece
  rw [enlargedVisitGreen_comp_eq_clipped A (visitActiveUnion c J) s T _
    ((enlargedVisitEntrance_ae_support A c J s T P hs hT n).mono
      fun _ hp => hp.1)]
  infer_instance

/-- Actual enlarged exit mixtures remain in the closed active interval. -/
theorem enlargedActiveExitMixture_ae_velocity (T : ℝ)
    (mu : Measure Point) :
    ∀ᵐ q ∂(enlargedVisitExitKernel A (visitActiveUnion c J) T ∘ₘ mu),
      q.velocity 0 ∈ closure c.active := by
  classical
  apply Measure.ae_comp_of_ae_ae
    (isClosed_closure.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)
  apply Filter.Eventually.of_forall
  intro p
  change ∀ᵐ q ∂(if hp : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) T then
    finiteUnionExit A (visitActiveUnion c J) T
      (enlargedVisitPole _ T ⟨p, hp⟩) else 0), q.velocity 0 ∈ closure c.active
  split
  · rename_i hp
    apply (visitUnionExit_ae_velocity A (visitActiveUnion c J) T
      (enlargedVisitPole _ T ⟨p, hp⟩)).mono
    intro q hq
    apply closure_mono _ hq
    rw [visitActiveUnion_carrier]
    exact inter_subset_left
  · rfl

end

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ)

/-- The quadratic is integrable against each finite enlarged active exit mixture. -/
theorem enlargedQuadratic_integrable_exit
    (mu : Measure Point) [IsFiniteMeasure mu] :
    Integrable (fun q => visitQuadratic c (q.velocity 0))
      (enlargedVisitExitKernel A (visitActiveUnion c J) T ∘ₘ mu) := 
  visitQuadratic_integrable_of_active_support c _ (enlargedActiveExitMixture_ae_velocity A c J T mu)

/-- The enlarged kernels satisfy the quadratic identity at every valid pole. -/
theorem enlargedQuadratic_pole_identity {p : Point}
    (hp : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) T) :
    visitQuadratic c (p.velocity 0) =
      (∫ q, visitQuadratic c (q.velocity 0) ∂enlargedVisitExitKernel A (visitActiveUnion c J) T p) +
      ∫ q, 2 * A.a (q.position 0) (q.velocity 0)
        ∂enlargedVisitGreenKernel A (visitActiveUnion c J) T p := by
  simpa only [enlargedVisitExitKernel, enlargedVisitGreenKernel, visitExtendKernel_apply_mem hp, enlargedVisitPole] using
    visitQuadratic_active_identity A c J T (enlargedVisitPole _ T ⟨p, hp⟩)

end

/-- Every actual entrance satisfies the integrated quadratic identity on its active domain. -/
theorem enlargedQuadratic_entrance_green_identity
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (P : Point)
    (hs : s ≤ P.time) (hT : P.time < T)
    (hJ : closure c.active ⊆ J.carrier) (n : ℕ) :
    (∫ p, visitQuadratic c (p.velocity 0)
      ∂enlargedVisitEntrance A c J s T P n) =
      (∫ p, visitQuadratic c (p.velocity 0)
        ∂(enlargedVisitExitKernel A (visitActiveUnion c J) T ∘ₘ
          enlargedVisitEntrance A c J s T P n)) +
      ∫ p, 2 * A.a (p.position 0) (p.velocity 0)
        ∂(enlargedVisitGreenKernel A (visitActiveUnion c J) T ∘ₘ
          enlargedVisitEntrance A c J s T P n) := by
  have : IsFiniteMeasure (enlargedVisitGreenKernel A (visitActiveUnion c J) T ∘ₘ
      enlargedVisitEntrance A c J s T P n) := enlargedActivePiece_isFiniteMeasure A c J s T P hs hT n
  refine integral_eq_comp_add (enlargedQuadratic_integrable_exit A c J T _)
    (visitCoefficient_integrable A _) ?_
  filter_upwards [enlargedVisitEntrance_ae_activePole A c J s T P hs hT hJ n] with p hp
  exact enlargedQuadratic_pole_identity A c J T hp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
