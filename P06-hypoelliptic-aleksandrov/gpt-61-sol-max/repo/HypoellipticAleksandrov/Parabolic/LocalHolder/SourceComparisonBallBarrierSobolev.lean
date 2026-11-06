module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonBallBarrier
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonSobolev
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonStationaryCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovGeometry
public import PDEFoundation.Calculus.RegularityOrder


/-! # Smooth H10 realizations of the Euclidean ball barrier

The zero-frontier quadratic belongs to H10 without an inset cutoff at the ball boundary.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set Matrix KineticAleksandrov
open scoped Matrix.Norms.Elementwise

variable {d : ℕ}

variable (lam M : ℝ) (A : CoefficientField d)

/-- The smooth forcing of the source-M spatial barrier. -/
def sourceBallBarrierForcing
    (z : TimeVelocity d) : ℝ :=
  -(2 * M * (A z.1 z.2).trace) / (2 * (d : ℝ) * lam)

/-- The trace forcing is smooth for smooth coefficients. -/
theorem contDiff_sourceBallBarrierForcing   (hA : IsSmoothCoefficient A) :
    ContDiff ℝ PDE.smoothOrder (sourceBallBarrierForcing lam M A) := (ContDiff.div_const
  (ContDiff.neg
    (ContDiff.mul contDiff_const
      (id
        (id
          (ContDiff.sum fun i a =>
            ContDiff.comp (contDiff_apply ℝ ℝ i) (ContDiff.comp (contDiff_apply ℝ (Fin d → ℝ) i) hA))))))
  (2 * ↑d * lam))

/-- The ball barrier has an actual smooth H10 realization with its literal trace forcing. -/
theorem exists_h10_sourceBallBarrier  (v₀ : PDE.Vec d) (r lam M : ℝ)
    (hr : 0 < r) (hlam : 0 < lam) (hM : 0 ≤ M) (A : CoefficientField d) :
    ∃ q : PDE.H10Function (PDE.euclideanBall v₀ r),
      ContDiff ℝ PDE.smoothOrder q.toH1Function.toFun ∧
      EqOn q.toH1Function.toFun (sourceBallBarrier v₀ r lam M)
        (closure (PDE.euclideanBall v₀ r)) ∧
      ∀ z : TimeVelocity d, z.2 ∈ PDE.euclideanBall v₀ r →
        scalarParabolicZeroOrderOperator A (fun _ _ => 0) (fun _ _ => 0)
          (fun z => q.toH1Function.toFun z.2) z = sourceBallBarrierForcing lam M A z := by
  obtain ⟨q, hq, _, hqe⟩ := exists_h10_smooth_barrier_eqOn
    (PDE.isOpen_euclideanBall v₀ r)
    (Occupation.isBounded_euclideanBall v₀ hr).isCompact_closure
    _ (contDiff_sourceBallBarrier v₀ r lam M)
    (fun y hy => sourceBallBarrier_nonneg v₀ r lam M hlam hM (subset_closure hy))
    (fun y hy => sourceBallBarrier_zero_frontier v₀ r lam M hy)
  refine ⟨q, hq, hqe, ?_⟩
  intro z hz
  rw [stationary_scalarOperator_eqOn (PDE.isOpen_euclideanBall v₀ r)
    q.toH1Function.toFun _
    (hqe.mono subset_closure) A z hz, scalarOperator_sourceBallBarrier]
  rfl

end HypoellipticAleksandrov.Parabolic.LocalHolder
