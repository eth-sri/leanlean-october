module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassEntranceIntegrals
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureFuture

/-! # Closed velocity support and quadratic integrability for actual active exit mixtures -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- Actual union exits remain in the closure of the physical union velocity carrier. -/
theorem visitUnionExit_ae_velocity
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : ℝ)
    (p : FiniteUnionPole H (T : WithTop ℝ)) :
    ∀ᵐ q ∂finiteUnionExit A H T p,
      q.velocity 0 ∈ closure H.carrier := by
  let I := H.component (finiteUnionPoleIndex H T p)
  filter_upwards [stripExitOfRealization_ae_closed_future A I
    (stripEvolution A I)
    (stripEvolution_spec A I) T (finiteUnionComponentPole H T p)] with q hq
  apply closure_mono (H.component_subset (finiteUnionPoleIndex H T p))
  change q.velocity 0 ∈ closure I.carrier
  simpa only [Interval.carrier, closure_Ioo I.ordered.ne] using hq.2.2

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)

/-- Every active exit kernel is concentrated on the closed active interval. -/
theorem visitActiveExitKernel_ae_velocity (p : Point) :
    ∀ᵐ q ∂visitUnionExitKernel A (visitActiveUnion c J) s T p,
      q.velocity 0 ∈ closure c.active := by
  classical
  change ∀ᵐ q ∂(if hp : p ∈ visitPoleSet (visitActiveUnion c J) s T then
    finiteUnionExit A (visitActiveUnion c J) T
      (visitPoleInclusion _ s T ⟨p, hp⟩) else 0), q.velocity 0 ∈ closure c.active
  split
  · rename_i hp
    apply (visitUnionExit_ae_velocity A (visitActiveUnion c J) T
      (visitPoleInclusion _ s T ⟨p, hp⟩)).mono
    intro q hq
    apply closure_mono _ hq
    rw [visitActiveUnion_carrier]
    exact inter_subset_left
  · simp

/-- Integrating the active exit family preserves its closed physical velocity support. -/
theorem visitActiveExitMixture_ae_velocity
    (mu : Measure Point) :
    ∀ᵐ q ∂(visitUnionExitKernel A (visitActiveUnion c J) s T ∘ₘ mu),
      q.velocity 0 ∈ closure c.active := by
  apply Measure.ae_comp_of_ae_ae
    (isClosed_closure.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)
  exact Filter.Eventually.of_forall
    (visitActiveExitKernel_ae_velocity A c J s T)

/-- The source quadratic is integrable against each finite actual active exit mixture. -/
theorem visitQuadratic_integrable_activeExitMixture
    (mu : Measure Point) [IsFiniteMeasure mu] :
    Integrable (fun q => visitQuadratic c (q.velocity 0))
      (visitUnionExitKernel A (visitActiveUnion c J) s T ∘ₘ mu) := 
  visitQuadratic_integrable_of_active_support c _ (visitActiveExitMixture_ae_velocity A c J s T mu)

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
