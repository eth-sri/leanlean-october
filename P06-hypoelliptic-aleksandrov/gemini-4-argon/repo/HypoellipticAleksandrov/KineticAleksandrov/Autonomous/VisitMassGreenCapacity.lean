module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassOuterBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationWaiting
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Capacity

/-! # The capacity bound for the actual sum of active visit occupations -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/- Actual active Green mixtures are supported in the open active velocity interval. -/
theorem visitActiveGreenMixture_ae_active
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (mu : Measure Point) :
    ∀ᵐ q ∂(visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ mu),
      q.velocity 0 ∈ c.active := by
  classical
  apply Measure.ae_comp_of_ae_ae
    (isOpen_Ioo.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable)
  apply Filter.Eventually.of_forall
  intro p
  change ∀ᵐ q ∂(if hp : p ∈ visitPoleSet (visitActiveUnion c J) s T then
    finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) T
      (visitPoleInclusion _ s T ⟨p, hp⟩) else 0), q.velocity 0 ∈ c.active
  split
  · rename_i hp
    exact (visitUnionGreen_ae_velocity hH hLE hlam hLam A (visitActiveUnion c J) T
      (visitPoleInclusion _ s T ⟨p, hp⟩)).mono fun q hq =>
        ((visitActiveUnion_carrier c J).le hq).1
  · simp

/- The partial sum of actual active Green masses has the source's velocity capacity bound. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
