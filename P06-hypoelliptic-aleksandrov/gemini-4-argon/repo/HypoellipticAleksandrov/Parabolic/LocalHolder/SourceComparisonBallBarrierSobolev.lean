module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonBallBarrier
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonSobolev
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonStationaryCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovGeometry

/-! # Smooth H10 realizations of the Euclidean ball barrier

The zero-frontier quadratic belongs to H10 without an inset cutoff at the ball boundary.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set Matrix KineticAleksandrov
open scoped Matrix.Norms.Elementwise

/- The smooth forcing of the source-M spatial barrier. -/
def sourceBallBarrierForcing {d } (lam M : ℝ) (A : CoefficientField d)
    (z : TimeVelocity d) : ℝ :=
  -(2 * M * (A z.1 z.2).trace) / (2 * (d : ℝ) * lam)

/- The trace forcing is smooth for smooth coefficients. -/
end HypoellipticAleksandrov.Parabolic.LocalHolder
