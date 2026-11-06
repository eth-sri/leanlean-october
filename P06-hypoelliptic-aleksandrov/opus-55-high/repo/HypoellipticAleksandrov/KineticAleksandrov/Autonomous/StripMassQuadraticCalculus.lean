module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EvolutionInstance
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonGrowth

/-! # The literal quadratic interval barrier in evolution coordinates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic

/-- Midpoint vector of the velocity interval. -/
def intervalMidpoint (H : Interval) : PDE.Vec 1 := fun _ => (H.lo + H.hi) / 2

/-- The quadratic barrier, written as an affine function of squared midpoint distance. -/
def stripQuadraticBarrier (H : Interval) (lam : ℝ) (p : Point) : ℝ :=
  (-1 / (2 * lam)) *
    (-(H.hi - H.lo) ^ 2 / 4 + PDE.vecNormSq (p.position - intervalMidpoint H))

variable (H : Interval) (lam : ℝ) (p : Point)

/-- The midpoint expression is exactly `(v-lo)(hi-v)/(2 lambda)`. -/
theorem stripQuadraticBarrier_eq  :
    stripQuadraticBarrier H lam p =
      (p.position 0 - H.lo) * (H.hi - p.position 0) / (2 * lam) := by
  simp only [stripQuadraticBarrier, PDE.vecNormSq_eq_sum_sq, Fin.sum_univ_one,
    Pi.sub_apply, intervalMidpoint]
  ring

/-- The interval barrier is nonnegative on the closed velocity interval. -/
theorem stripQuadraticBarrier_nonneg  {lam : ℝ} (hlam : 0 < lam)
    (p : Point) (hp : H.lo ≤ p.position 0 ∧ p.position 0 ≤ H.hi) :
    0 ≤ stripQuadraticBarrier H lam p := by
  rw [stripQuadraticBarrier_eq]
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hp.1) (sub_nonneg.mpr hp.2))
    (by positivity)

/-- The barrier has the regularity needed by the growth comparison theorem. -/
theorem stripQuadraticBarrier_regular  :
    IsSliceRegularAt (stripQuadraticBarrier H lam) p := by
  unfold stripQuadraticBarrier
  refine ⟨?_, ?_, ?_⟩
  · simp
  · exact (contDiff_const.mul
      (contDiff_const.add (contDiff_vecNormSq_sub _))).contDiffAt
  · change ContDiffAt ℝ 2 (fun _ : PDE.Vec 1 =>
      (-1 / (2 * lam)) * (-(H.hi - H.lo) ^ 2 / 4 +
        PDE.vecNormSq (p.position - intervalMidpoint H))) p.velocity
    fun_prop

/-- The transported forward operator of the barrier is exactly `-a/lambda`. -/
theorem stripQuadraticBarrier_operator (a : ℝ → ℝ → ℝ) (H : Interval)
    (lam : ℝ) (p : Point) :
    transportedForwardOperator (evolutionCoefficient a) (SectionTwo.identityDrift 1)
      (stripQuadraticBarrier H lam) p = -a (p.velocity 0) (p.position 0) / lam := by
  have hslice : (fun y : PDE.Vec 1 => stripQuadraticBarrier H lam
      ⟨p.time, y, p.velocity⟩) = fun y =>
      (fun s : ℝ => (-1 / (2 * lam)) * (-(H.hi - H.lo) ^ 2 / 4 + s))
        (PDE.vecNormSq (y - intervalMidpoint H)) := rfl
  have hd := matrixContraction_sliceHessian_comp_vecNormSq_sub
    (m := intervalMidpoint H) (x := p.position)
    (contDiffAt_affine_weight (-1 / (2 * lam)) (-(H.hi - H.lo) ^ 2 / 4) _)
    (evolutionCoefficient a p.time p.position p.velocity)
  rw [transportedForwardOperator_apply]
  unfold fullKineticCoefficientAt
  rw [diffusedHessian_eq_sliceHessian, hslice, hd]
  have hgrad : kineticVelocityGradient (stripQuadraticBarrier H lam) p = 0 := by
    ext i
    change fderiv ℝ (fun _ : PDE.Vec 1 =>
      (-1 / (2 * lam)) * (-(H.hi - H.lo) ^ 2 / 4 +
        PDE.vecNormSq (p.position - intervalMidpoint H))) p.velocity _ = 0
    simp
  rw [hgrad]
  simp only [kineticTimeDerivative, stripQuadraticBarrier, deriv_const,
    deriv_affine_weight, PDE.vecDot, Pi.zero_apply, Matrix.trace, Matrix.diag, Fin.sum_univ_one,
    evolutionCoefficient]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
