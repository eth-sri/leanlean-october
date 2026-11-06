module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffClassical
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.BarrierPackedJets
import Mathlib.Tactic.Ring

/-! # The favorable convexity term in the cutoff source equation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open HypoellipticAleksandrov.Parabolic MeasureTheory
open scoped MatrixOrder

/- Contraction of the full positive second-chain representative. -/
theorem contraction_cutoff_identity {d } (A B : PDE.Mat d)
    (w : PDE.Vec d) (s t : ℝ) :
    matrixContraction A (fun i k => s * B i k + t * w i * w k) =
      s * matrixContraction A B + t * PDE.vecDot (A.mulVec w) w := by
  simpa only [neg_neg, neg_mul, sub_neg_eq_add] using
    contraction_flattening_identity A B w (-s) (-t)

/- Contraction distributes over an entrywise difference. -/
theorem contraction_sub_right {d } (A B C : PDE.Mat d) :
    matrixContraction A (fun i k => B i k - C i k) =
      matrixContraction A B - matrixContraction A C := by
  simp only [matrixContraction, mul_sub, Finset.sum_sub_distrib]

/- The cutoff source representative uses the actual first and second weak jets.
The time derivative of the stationary profile vanishes. -/
def timeCutoffSourceRepresentative {d alpha}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ) (P : KineticPoint d) : ℝ :=
  let q := (P.position, P.velocity)
  let s := selectedFlatProfile h r q - barrier mu R P
  let w := flatProfileVelocityJet h r q - kineticVelocityGradient (barrier mu R) P
  (-(deriv timeCutoffTheta s) * kineticTimeDerivative (barrier mu R) P) +
    PDE.vecDot P.velocity (fun i => deriv timeCutoffTheta s * flatProfilePositionJet h r q i) -
    matrixContraction (profileMatrix h q) (fun i k =>
      deriv timeCutoffTheta s *
        (flatProfileHessian h r q i k - kineticVelocityHessian (barrier mu R) P i k) +
      deriv (deriv timeCutoffTheta) s * w i * w k)

/- The exact source identity has a nonpositive quadratic correction. -/
theorem flatSource_nonneg_ae_of_profile {d alpha}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) :
    ∀ᵐ q ∂volume, 0 ≤ flatSource (profileMatrix h) (profileFunction h)
      flatteningPsi alpha r q := by
  obtain ⟨hlam, _, _, _, _, hA, _⟩ := selectedProfile_spec h
  filter_upwards [flatSource_ae_eq_jet_of_profile h r] with q hq
  rw [hq]
  unfold flatSourceWithJet
  exact mul_nonneg
    (mul_nonneg (Real.rpow_pos_of_pos hr _).le (flatteningPsi_deriv2_nonneg _))
    (quadratic_nonneg_of_loewner _ hlam.le _ (hA q).1 _)

/- The favorable convexity term and barrier sign bound the weak source by the shell source. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
