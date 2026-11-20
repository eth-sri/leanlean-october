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

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
  (P : Point) (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier)
include lam Lam A c J s T P hP

/-- Every actual entrance satisfies the integrated quadratic identity on its active domain. -/
theorem visitQuadratic_entrance_green_identity (n : ℕ) :
    (∫ p, visitQuadratic c (p.velocity 0)
      ∂visitEntrancePiece A c J s T P n) =
      (∫ p, visitQuadratic c (p.velocity 0)
        ∂(visitUnionExitKernel A (visitActiveUnion c J) s T ∘ₘ
          visitEntrancePiece A c J s T P n)) +
      ∫ p, 2 * A.a (p.position 0) (p.velocity 0)
        ∂(visitUnionGreenKernel A (visitActiveUnion c J) s T ∘ₘ
          visitEntrancePiece A c J s T P n) := by
  refine integral_eq_comp_add (visitQuadratic_integrable_activeExitMixture A c J s T _)
    (visitCoefficient_integrable A _) ?_
  filter_upwards [visitEntrancePiece_ae_activePole A c J s T P hP n] with p hp
  simpa only [visitUnionExitKernel, visitUnionGreenKernel, visitExtendKernel_apply_mem hp, visitPoleInclusion] using
    visitQuadratic_active_identity A c J T (visitPoleInclusion _ s T ⟨p, hp⟩)

/-- The genuine per-entrance count inequality follows from the actual quadratic Green identity. -/
theorem visitQuadratic_entrance_mass_bound (n : ℕ) :
    let mu := visitEntrancePiece A c J s T P n
    let E := visitUnionExitKernel A (visitActiveUnion c J) s T
    let G := visitUnionGreenKernel A (visitActiveUnion c J) s T
    let B := visitBoundary s T (visitActiveInterval c) J
    5 * c.r ^ 2 / 16 * (mu univ).toReal ≤
      9 * c.r ^ 2 / 16 * (((E ∘ₘ mu).restrict Bᶜ) univ).toReal +
        2 * Lam * ((G ∘ₘ mu) univ).toReal := by
  dsimp only
  let mu := visitEntrancePiece A c J s T P n
  let E := visitUnionExitKernel A (visitActiveUnion c J) s T
  let G := visitUnionGreenKernel A (visitActiveUnion c J) s T
  let B := visitBoundary s T (visitActiveInterval c) J
  have hiE := visitQuadratic_integrable_activeExitMixture A c J s T mu
  have hi := integral_mono_ae
    (hiE.restrict (s := Bᶜ))
    (integrable_const (9 * c.r ^ 2 / 16))
    (Filter.Eventually.of_forall (fun p => visitQuadratic_le c (p.velocity 0)))
  have hx : (∫ p, visitQuadratic c (p.velocity 0) ∂(E ∘ₘ mu).restrict Bᶜ) ≤
      9 * c.r ^ 2 / 16 * (((E ∘ₘ mu).restrict Bᶜ) univ).toReal := by
    simpa only [integral_const, smul_eq_mul, Measure.real, mul_comm] using hi
  have hz : (∫ p, visitQuadratic c (p.velocity 0) ∂(E ∘ₘ mu).restrict B) = 0 :=
    visitQuadratic_outgoing_integral_zero A c J s T P n
  have hs := integral_add_compl (measurableSet_visitBoundary s T (visitActiveInterval c) J) hiE
  rw [hz, zero_add] at hs
  have hxfull := hs.symm.le.trans hx
  exact (visitQuadratic_entrance_integral_lower A c J s T P n).trans
    ((visitQuadratic_entrance_green_identity A c J s T P hP n).le.trans
      (add_le_add hxfull (visitCoefficient_integral_le A (G ∘ₘ mu))))

/-- Summing actual entrance estimates gives the finite quadratic counting inequality. -/
theorem visitQuadratic_partial_mass_bound (N : ℕ) :
    let mu := visitEntrancePiece A c J s T P
    let E := visitUnionExitKernel A (visitActiveUnion c J) s T
    let G := visitUnionGreenKernel A (visitActiveUnion c J) s T
    let B := visitBoundary s T (visitActiveInterval c) J
    5 * c.r ^ 2 / 16 * (∑ n ∈ Finset.range N, (mu n univ).toReal) ≤
      9 * c.r ^ 2 / 16 *
        (∑ n ∈ Finset.range N, (((E ∘ₘ mu n).restrict Bᶜ) univ).toReal) +
      2 * Lam * (∑ n ∈ Finset.range N, ((G ∘ₘ mu n) univ).toReal) := by
  have h := Finset.sum_le_sum (s := Finset.range N)
    (fun n _ => visitQuadratic_entrance_mass_bound A c J s T P hP n)
  dsimp only at h ⊢
  simpa only [Finset.mul_sum, Finset.sum_add_distrib] using h

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
