module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitTimeIntegrals
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassOutgoing
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral

/-! # The actual short-time quadratic identity integrated over entrance measures -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (c : Clock) (J : Interval) (s T b : ℝ) (P : Point)
    (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (n : ℕ)

/-- The localized quadratic is integrable against every actual entrance measure. -/
theorem visitTimeQuadratic_integrable_entrance :
    Integrable (fun p => visitTimeCutoff b c.r c.positive p.time *
      visitQuadratic c (p.velocity 0))
      (visitEntrancePiece hlam hLam A c J s T P n) := by
  apply visitTimeQuadratic_integrable_of_active_support
  exact (visitGamma_ae_closedEntrance P c J s T _ _ n).mono
    (fun p hp => subset_closure (visitClosedEntrance_subset_active c hp))

/-- The localized quadratic also has exactly zero outgoing internal-face integral. -/
theorem visitTimeQuadratic_outgoing_integral_zero :
    (∫ p, visitTimeCutoff b c.r c.positive p.time * visitQuadratic c (p.velocity 0)
      ∂visitOutgoingPiece hlam hLam A c J s T P n) = 0 := by
  have hz : (fun p => visitTimeCutoff b c.r c.positive p.time *
      visitQuadratic c (p.velocity 0)) =ᵐ[
        visitOutgoingPiece hlam hLam A c J s T P n] 0 := by
    filter_upwards [visitQuadratic_ae_zero_outgoing hlam hLam A c J s T P n] with p hp
    simp_all
  rw [integral_congr_ae hz]
  apply integral_zero

include hP in
/-- Every actual entrance satisfies the genuine integrated short-time quadratic identity. -/
theorem visitTimeQuadratic_entrance_green_identity :
    let mu := visitEntrancePiece hlam hLam A c J s T P n
    let E := visitUnionExitKernel hlam hLam A (visitActiveUnion c J) s T
    let G := visitUnionGreenKernel hlam hLam A (visitActiveUnion c J) s T
    let f := fun q : Point => visitTimeCutoff b c.r c.positive q.time *
      visitQuadratic c (q.velocity 0)
    (∫ p, f p ∂mu) = (∫ p, f p ∂E ∘ₘ mu) -
      ∫ p, forwardScalarOperator A.a f p ∂G ∘ₘ mu := by
  classical
  dsimp only
  let mu := visitEntrancePiece hlam hLam A c J s T P n
  let E := visitUnionExitKernel hlam hLam A (visitActiveUnion c J) s T
  let G := visitUnionGreenKernel hlam hLam A (visitActiveUnion c J) s T
  let f := fun q : Point => visitTimeCutoff b c.r c.positive q.time *
    visitQuadratic c (q.velocity 0)
  let g := fun p => forwardScalarOperator A.a f p
  have hE :=
    visitTimeQuadratic_integrable_activeExitMixture hlam hLam A c J s T b mu
  have hG :=
    visitTimeQuadratic_operator_integrable_activeGreenMixture hlam hLam A c J s T b mu
  have hiE : Integrable (fun p => ∫ q, f q ∂E p) mu := by
    rw [Measure.comp_eq_comp_const_apply] at hE
    exact hE.integral_comp
  have hiG : Integrable (fun p => ∫ q, g q ∂G p) mu := by
    rw [Measure.comp_eq_comp_const_apply] at hG
    exact hG.integral_comp
  have hp : f =ᵐ[mu] fun p => (∫ q, f q ∂E p) - ∫ q, g q ∂G p := by
    filter_upwards [visitEntrancePiece_ae_activePole hlam hLam A c J s T P hP n]
      with p hp
    let ep := visitPoleInclusion (visitActiveUnion c J) s T ⟨p, hp⟩
    have he : E p = finiteUnionExit hlam hLam A (visitActiveUnion c J) T ep := by
      change (if ht : p ∈ visitPoleSet (visitActiveUnion c J) s T then
        finiteUnionExit hlam hLam A (visitActiveUnion c J) T
          (visitPoleInclusion _ s T ⟨p, ht⟩) else 0) = _
      rw [dite_eq_left hp]
    have hg : G p = finiteUnionGreen hlam hLam A (visitActiveUnion c J) T ep := by
      change (if ht : p ∈ visitPoleSet (visitActiveUnion c J) s T then
        finiteUnionGreen hlam hLam A (visitActiveUnion c J) T
          (visitPoleInclusion _ s T ⟨p, ht⟩) else 0) = _
      rw [dite_eq_left hp]
    have hh := visitTimeQuadratic_active_identity hlam hLam A c J b T ep
    aesop
  rw [integral_congr_ae hp, integral_sub hiE hiG]
  rw [nested_integral_bind mu E E.measurable f hE,
    nested_integral_bind mu G G.measurable g hG]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
