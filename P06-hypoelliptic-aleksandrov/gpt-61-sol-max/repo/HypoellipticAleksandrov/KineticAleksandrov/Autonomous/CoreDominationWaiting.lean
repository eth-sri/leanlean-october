module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalSetting
import Mathlib.Tactic

/-! # Actual waiting-domain occupation gives no mass to core velocities -/

 public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory ProbabilityTheory

variable (c : Clock)

/-- The core lies in the closed entrance interval. -/
theorem visitCore_subset_closedEntrance  : c.core ⊆ closure c.entrance := by

  rw [Clock.entrance, closure_Ioo (show c.vbar - c.r / 2 < c.vbar + c.r / 2 by linarith [c.positive]).ne]
  intro v hv
  change c.vbar - c.r / 2 ≤ v ∧ v ≤ c.vbar + c.r / 2
  constructor <;> linarith [hv.1, hv.2, c.positive]

/-- The actual waiting union is disjoint from the core. -/
theorem visitWaiting_disjoint_core  (J : Interval) :
    Disjoint (visitWaitingUnion c J).carrier c.core := by
  rw [visitWaitingUnion_carrier]
  exact Set.disjoint_left.mpr fun v hv hc => hv.2 (visitCore_subset_closedEntrance c hc)

variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)

/-- Actual componentwise Green measures are supported in the union's velocity carrier. -/
theorem visitUnionGreen_ae_velocity
     (H : FiniteIntervalUnion) (T : ℝ)
    (p : FiniteUnionPole H (T : WithTop ℝ)) :
    ∀ᵐ q ∂finiteUnionGreen hH hLE hlam hLam A H T p, q.velocity 0 ∈ H.carrier := (stripGreenOfKernel_ae_mem_stripPast
    (H.component (finiteUnionPoleIndex H T p)) _ T (finiteUnionComponentPole H T p)).mono
      (fun _ hq => H.component_subset _ hq.2)

variable (c : Clock) (J : Interval) (s T : ℝ)

/-- Every actual waiting Green kernel gives zero occupation to the core. -/
theorem visitWaitingGreenKernel_core_zero
      (p : Point) :
    visitUnionGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) s T p
      {q | q.velocity 0 ∈ c.core} = 0 := by
  classical
  change (if hp : p ∈ visitPoleSet (visitWaitingUnion c J) s T then
    finiteUnionGreen hH hLE hlam hLam A _ T
      (visitPoleInclusion _ s T ⟨p, hp⟩) else 0) {q | q.velocity 0 ∈ c.core} = 0
  split
  · rename_i hp
    have hae := visitUnionGreen_ae_velocity hH hLE hlam hLam A _ T
      (visitPoleInclusion _ s T ⟨p, hp⟩)

    apply le_antisymm _ zero_le
    apply (measure_mono (show {q : Point | q.velocity 0 ∈ c.core} ⊆
        {q | q.velocity 0 ∉ (visitWaitingUnion c J).carrier} from
      fun _ hc hv => Set.disjoint_left.mp (visitWaiting_disjoint_core c J) hv hc)).trans_eq (ae_iff.mp hae)
  · rfl

/-- Integrating any starting measure against the actual waiting kernel still avoids the core. -/
theorem visitWaitingGreenMixture_core_zero
      (mu : Measure Point) :
    (visitUnionGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) s T ∘ₘ mu)
      {q | q.velocity 0 ∈ c.core} = 0 := by
  have hC : MeasurableSet {q : Point | q.velocity 0 ∈ c.core} :=
    isClosed_Icc.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable
  rw [Measure.bind_apply hC (Kernel.aemeasurable _)]
  simp only [visitWaitingGreenKernel_core_zero, lintegral_zero]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
