module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EvolutionInstance
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonGrowth

/-! # The literal quadratic interval barrier in evolution coordinates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic

/- Midpoint vector of the velocity interval. -/
def intervalMidpoint (H : Interval) : PDE.Vec 1 := fun _ => (H.lo + H.hi) / 2

/- The quadratic barrier, written as an affine function of squared midpoint distance. -/
def stripQuadraticBarrier (H : Interval) (lam : ℝ) (p : Point) : ℝ :=
  (-1 / (2 * lam)) *
    (-(H.hi - H.lo) ^ 2 / 4 + PDE.vecNormSq (p.position - intervalMidpoint H))

/- The midpoint expression is exactly `(v-lo)(hi-v)/(2 lambda)`. -/
theorem stripQuadraticBarrier_eq (H : Interval) (lam : ℝ) (p : Point) :
    stripQuadraticBarrier H lam p =
      (p.position 0 - H.lo) * (H.hi - p.position 0) / (2 * lam) := by
  simp only [stripQuadraticBarrier, PDE.vecNormSq_eq_sum_sq, Fin.sum_univ_one,
    Pi.sub_apply, intervalMidpoint]
  ring

/- The interval barrier is nonnegative on the closed velocity interval. -/
theorem stripQuadraticBarrier_nonneg (H : Interval) {lam } (hlam : 0 < lam)
    (p : Point) (hp : H.lo ≤ p.position 0 ∧ p.position 0 ≤ H.hi) :
    0 ≤ stripQuadraticBarrier H lam p := by
  rw [stripQuadraticBarrier_eq]
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hp.1) (sub_nonneg.mpr hp.2))
    (by positivity)

/- The barrier has the regularity needed by the growth comparison theorem. -/
theorem stripQuadraticBarrier_regular (H : Interval) (lam : ℝ) (p : Point) :
    IsSliceRegularAt (stripQuadraticBarrier H lam) p := by
  unfold stripQuadraticBarrier
  refine ⟨?_, ?_, ?_⟩
  · change DifferentiableAt ℝ (fun _ : ℝ =>
      (-1 / (2 * lam)) * (-(H.hi - H.lo) ^ 2 / 4 +
        PDE.vecNormSq (p.position - intervalMidpoint H))) p.time
    exact differentiableAt_const _
  · exact (contDiff_const.mul
      (contDiff_const.add (contDiff_vecNormSq_sub (intervalMidpoint H)))).contDiffAt
  · change ContDiffAt ℝ 2 (fun _ : PDE.Vec 1 =>
      (-1 / (2 * lam)) * (-(H.hi - H.lo) ^ 2 / 4 +
        PDE.vecNormSq (p.position - intervalMidpoint H))) p.velocity
    exact contDiffAt_const

/- The transported forward operator of the barrier is exactly `-a/lambda`. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
