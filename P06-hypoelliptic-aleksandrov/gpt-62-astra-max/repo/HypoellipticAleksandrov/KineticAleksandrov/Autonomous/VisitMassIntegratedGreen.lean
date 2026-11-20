module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassExitIntegrals
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassCoefficientIntegral
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassOutgoing
import Mathlib.Tactic

/-! # The genuine quadratic Green identity integrated over each actual entrance -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (c : Clock) (J : Interval) (s T : ℝ) (P : Point)
    (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (n : ℕ)
include hP

/-- Every actual entrance satisfies the integrated quadratic identity on its active domain. -/
theorem visitQuadratic_entrance_green_identity :
    (∫ p, visitQuadratic c (p.velocity 0)
      ∂visitEntrancePiece hlam hLam A c J s T P n) =
      (∫ p, visitQuadratic c (p.velocity 0)
        ∂(visitUnionExitKernel hlam hLam A (visitActiveUnion c J) s T ∘ₘ
          visitEntrancePiece hlam hLam A c J s T P n)) +
      ∫ p, 2 * A.a (p.position 0) (p.velocity 0)
        ∂(visitUnionGreenKernel hlam hLam A (visitActiveUnion c J) s T ∘ₘ
          visitEntrancePiece hlam hLam A c J s T P n) := by
  classical
  let mu := visitEntrancePiece hlam hLam A c J s T P n
  let E := visitUnionExitKernel hlam hLam A (visitActiveUnion c J) s T
  let G := visitUnionGreenKernel hlam hLam A (visitActiveUnion c J) s T
  let f := fun p : Point => visitQuadratic c (p.velocity 0)
  let g := fun p : Point => 2 * A.a (p.position 0) (p.velocity 0)
  have hE :=
    visitQuadratic_integrable_activeExitMixture hlam hLam A c J s T mu
  have hG : Integrable g (G ∘ₘ mu) := visitCoefficient_integrable hlam A _
  have hiE : Integrable (fun p => ∫ q, f q ∂E p) mu := by
    rw [Measure.comp_eq_comp_const_apply] at hE
    exact hE.integral_comp
  have hiG : Integrable (fun p => ∫ q, g q ∂G p) mu := by
    rw [Measure.comp_eq_comp_const_apply] at hG
    exact hG.integral_comp
  have hp : f =ᵐ[mu] fun p => (∫ q, f q ∂E p) + ∫ q, g q ∂G p := by
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
    have hh := visitQuadratic_active_identity hlam hLam A c J T ep
    have hn : (fun q : Point => -2 * A.a (q.position 0) (q.velocity 0)) = -g := by
      funext q
      dsimp [g]
      ring
    rw [← he, ← hg, hn] at hh
    change f p = (∫ q, f q ∂E p) - ∫ q, -g q ∂G p at hh
    rw [integral_neg, sub_neg_eq_add] at hh
    exact hh
  rw [integral_congr_ae hp, integral_add hiE hiG]
  rw [nested_integral_bind mu E E.measurable f hE,
    nested_integral_bind mu G G.measurable g hG]

/-- The genuine per-entrance count inequality follows from the actual quadratic Green identity. -/
theorem visitQuadratic_entrance_mass_bound :
    let mu := visitEntrancePiece hlam hLam A c J s T P n
    let E := visitUnionExitKernel hlam hLam A (visitActiveUnion c J) s T
    let G := visitUnionGreenKernel hlam hLam A (visitActiveUnion c J) s T
    let B := visitBoundary s T (visitActiveInterval c) J
    5 * c.r ^ 2 / 16 * (mu univ).toReal ≤
      9 * c.r ^ 2 / 16 * (((E ∘ₘ mu).restrict Bᶜ) univ).toReal +
        2 * Lam * ((G ∘ₘ mu) univ).toReal := by
  dsimp only
  let mu := visitEntrancePiece hlam hLam A c J s T P n
  let E := visitUnionExitKernel hlam hLam A (visitActiveUnion c J) s T
  let B := visitBoundary s T (visitActiveInterval c) J
  have hiE := visitQuadratic_integrable_activeExitMixture hlam hLam A c J s T mu
  have hx : (∫ p, visitQuadratic c (p.velocity 0) ∂(E ∘ₘ mu).restrict Bᶜ) ≤
      9 * c.r ^ 2 / 16 * (((E ∘ₘ mu).restrict Bᶜ) univ).toReal := by
    simpa only [integral_const, smul_eq_mul, Measure.real, mul_comm] using (integral_mono_ae (hiE.restrict (s := Bᶜ)) (integrable_const (9 * c.r ^ 2 / 16)) (Filter.Eventually.of_forall (fun p => visitQuadratic_le c (p.velocity 0))))
  have hz : (∫ p, visitQuadratic c (p.velocity 0) ∂(E ∘ₘ mu).restrict B) = 0 :=
    visitQuadratic_outgoing_integral_zero hlam hLam A c J s T P n
  have hs := integral_add_compl (measurableSet_visitBoundary s T (visitActiveInterval c) J) hiE
  rw [hz, zero_add] at hs
  exact (visitQuadratic_entrance_integral_lower hlam hLam A c J s T P n).trans
    ((visitQuadratic_entrance_green_identity hlam hLam A c J s T P hP n).le.trans
      (add_le_add (hs.symm.le.trans hx) (visitCoefficient_integral_le hlam A ((visitUnionGreenKernel hlam hLam A (visitActiveUnion c J) s T) ∘ₘ mu))))

/-- Summing actual entrance estimates gives the finite quadratic counting inequality. -/
theorem visitQuadratic_partial_mass_bound (N : ℕ) :
    let mu := visitEntrancePiece hlam hLam A c J s T P
    let E := visitUnionExitKernel hlam hLam A (visitActiveUnion c J) s T
    let G := visitUnionGreenKernel hlam hLam A (visitActiveUnion c J) s T
    let B := visitBoundary s T (visitActiveInterval c) J
    5 * c.r ^ 2 / 16 * (∑ n ∈ Finset.range N, (mu n univ).toReal) ≤
      9 * c.r ^ 2 / 16 *
        (∑ n ∈ Finset.range N, (((E ∘ₘ mu n).restrict Bᶜ) univ).toReal) +
      2 * Lam * (∑ n ∈ Finset.range N, ((G ∘ₘ mu n) univ).toReal) := by
  have h := Finset.sum_le_sum (s := Finset.range N)
    (fun n _ => visitQuadratic_entrance_mass_bound hlam hLam A c J s T P hP n)
  simpa only [Finset.mul_sum, Finset.sum_add_distrib] using h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
