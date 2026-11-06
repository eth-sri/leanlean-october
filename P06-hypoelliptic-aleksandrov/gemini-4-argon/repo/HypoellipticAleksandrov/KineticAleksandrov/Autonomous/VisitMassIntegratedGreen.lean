module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassExitIntegrals
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassCoefficientIntegral
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassOutgoing
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassQuadratic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalSupport

/-! # The genuine quadratic Green identity integrated over each actual entrance -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open scoped Classical

/- Every actual entrance satisfies the integrated quadratic identity on its active domain. -/
theorem visitQuadratic_entrance_mass_bound
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (P : Point)
    (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (n : ℕ) :
    let mu := visitEntrancePiece hH hLE hlam hLam A c J s T P n
    let E := visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
    let G := visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
    let B := visitBoundary s T (visitActiveInterval c) J
    5 * c.r ^ 2 / 16 * (mu univ).toReal ≤
      9 * c.r ^ 2 / 16 * (((E ∘ₘ mu).restrict Bᶜ) univ).toReal +
        2 * Lam * ((G ∘ₘ mu) univ).toReal := by
  dsimp only
  let mu := visitEntrancePiece hH hLE hlam hLam A c J s T P n
  let E := visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
  let G := visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
  let B := visitBoundary s T (visitActiveInterval c) J
  have hiE := visitQuadratic_integrable_activeExitMixture hH hLE hlam hLam A c J s T mu
  have hi := integral_mono_ae
    (hiE.restrict (s := Bᶜ))
    (integrable_const (9 * c.r ^ 2 / 16))
    (Filter.Eventually.of_forall (fun p => visitQuadratic_le c (p.velocity 0)))
  have hx : (∫ p, visitQuadratic c (p.velocity 0) ∂(E ∘ₘ mu).restrict Bᶜ) ≤
      9 * c.r ^ 2 / 16 * (((E ∘ₘ mu).restrict Bᶜ) univ).toReal := by
    simpa only [integral_const, smul_eq_mul, Measure.real, mul_comm] using hi
  have hz : (∫ p, visitQuadratic c (p.velocity 0) ∂(E ∘ₘ mu).restrict B) = 0 :=
    visitQuadratic_outgoing_integral_zero hH hLE hlam hLam A c J s T P n
  have hs := integral_add_compl (measurableSet_visitBoundary s T (visitActiveInterval c) J) hiE
  rw [hz, zero_add] at hs
  have hxfull := hs.symm.le.trans hx
  have _h_xinl_0 : 5 * c.r ^ 2 / 16 * (visitEntrancePiece hH hLE hlam hLam A c J s T P n univ).toReal ≤
      ∫ p, visitQuadratic c (p.velocity 0)
        ∂visitEntrancePiece hH hLE hlam hLam A c J s T P n := by
    have hi : Integrable (fun p => visitQuadratic c (p.velocity 0))
        (visitEntrancePiece hH hLE hlam hLam A c J s T P n) := by
        have hc : Continuous (fun p : Point => visitQuadratic c (p.velocity 0)) :=
          (visitQuadratic_smooth c).continuous.comp ((continuous_apply 0).comp continuous_velocity)
        apply Integrable.mono' (integrable_const (9 * c.r ^ 2 / 16)) hc.measurable.aestronglyMeasurable
        filter_upwards [visitGamma_ae_closedEntrance P c J s T
          (visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T)
          (visitUnionExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) s T) n] with p hp
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact visitQuadratic_le c _
        · exact (by positivity : 0 ≤ 5 * c.r ^ 2 / 16).trans
            (visitQuadratic_entrance_lower c hp)

      /- The exact five-sixteenths lower bound survives integration, with the initial atom included. -/
    have hb := integral_mono_ae (integrable_const (5 * c.r ^ 2 / 16)) hi (by
      filter_upwards [visitGamma_ae_closedEntrance P c J s T
        (visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T)
        (visitUnionExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) s T) n] with p hp
      exact visitQuadratic_entrance_lower c hp)
    simpa only [integral_const, smul_eq_mul, Measure.real, mul_comm] using hb
  have _h_inl_12 : (∫ p, visitQuadratic c (p.velocity 0) ∂visitEntrancePiece hH hLE hlam hLam A c J s T P n) = (∫ p, visitQuadratic c (p.velocity 0) ∂(visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ visitEntrancePiece hH hLE hlam hLam A c J s T P n)) + ∫ p, 2 * A.a (p.position 0) (p.velocity 0) ∂(visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ visitEntrancePiece hH hLE hlam hLam A c J s T P n) := by
    classical
    let mu := visitEntrancePiece hH hLE hlam hLam A c J s T P n
    let E := visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
    let G := visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
    let f := fun p : Point => visitQuadratic c (p.velocity 0)
    let g := fun p : Point => 2 * A.a (p.position 0) (p.velocity 0)
    have hE :=
      visitQuadratic_integrable_activeExitMixture hH hLE hlam hLam A c J s T mu
    have hG : Integrable g (G ∘ₘ mu) := visitCoefficient_integrable hlam A _
    have hiE : Integrable (fun p => ∫ q, f q ∂E p) mu := by
      rw [Measure.comp_eq_comp_const_apply] at hE
      simpa only [Kernel.const_apply] using hE.integral_comp
    have hiG : Integrable (fun p => ∫ q, g q ∂G p) mu := by
      rw [Measure.comp_eq_comp_const_apply] at hG
      simpa only [Kernel.const_apply] using hG.integral_comp
    have hp : f =ᵐ[mu] fun p => (∫ q, f q ∂E p) + ∫ q, g q ∂G p := by
      filter_upwards [visitEntrancePiece_ae_activePole hH hLE hlam hLam A c J s T P hP n]
        with p hp
      let ep := visitPoleInclusion (visitActiveUnion c J) s T ⟨p, hp⟩
      have he : E p = finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) T ep := by
        change (if ht : p ∈ visitPoleSet (visitActiveUnion c J) s T then
          finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) T
            (visitPoleInclusion _ s T ⟨p, ht⟩) else 0) = _
        rw [dite_eq_left hp]
      have hg : G p = finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) T ep := by
        change (if ht : p ∈ visitPoleSet (visitActiveUnion c J) s T then
          finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) T
            (visitPoleInclusion _ s T ⟨p, ht⟩) else 0) = _
        rw [dite_eq_left hp]
      have hh := visitQuadratic_active_identity hH hLE hlam hLam A c J T ep
      have hn : (fun q : Point => -2 * A.a (q.position 0) (q.velocity 0)) = -g := by
        funext q
        dsimp [g]
        ring
      rw [← he, ← hg, hn] at hh
      change f p = (∫ q, f q ∂E p) - ∫ q, -g q ∂G p at hh
      rw [integral_neg, sub_neg_eq_add] at hh
      exact hh
    change (∫ p, f p ∂mu) = (∫ p, f p ∂E ∘ₘ mu) + ∫ p, g p ∂G ∘ₘ mu
    rw [integral_congr_ae hp, integral_add hiE hiG]
    rw [nested_integral_bind mu E E.measurable f hE,
      nested_integral_bind mu G G.measurable g hG]
  exact _h_xinl_0.trans
    (_h_inl_12.le.trans
      (add_le_add hxfull (visitCoefficient_integral_le hlam A (G ∘ₘ mu))))

/- Summing actual entrance estimates gives the finite quadratic counting inequality. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
