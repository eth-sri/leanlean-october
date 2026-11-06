module

public import HypoellipticAleksandrov.Parabolic.SourceLocalHarnackScaling
public import HypoellipticAleksandrov.Parabolic.HarnackStability
public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.CoefficientExtension

/-! # Local weak Harnack inequalities on closed link boxes -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology Matrix.Norms.Elementwise

/- Smooth coefficients and values have a continuous parabolic residual. -/
theorem continuous_parabolicOperator_of_smooth_for_unitCylinder
    {d B} {q : TimeVelocity d → ℝ}
    (hB : IsSmoothCoefficient B)
    (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q) :
    Continuous (fun z => parabolicOperator B q z) := by
  change Continuous (fun x =>
    timeDerivative q x - matrixContraction (coefficientAt B x) (velocityHessian q x))
  apply Continuous.sub
  · unfold timeDerivative
    exact ((hq.contDiff_fderiv_apply (m := 0) (by norm_num)).comp
      (contDiff_id.prodMk contDiff_const)).continuous
  · unfold matrixContraction
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    apply Continuous.mul
    · exact hB.continuous.matrix_elem i j
    · unfold velocityHessian
      have hfirst : ContDiff ℝ 1 (fderiv ℝ q) :=
        hq.fderiv_right (m := 1) (by exact WithTop.coe_le_coe.mpr le_top)
      simpa using (hfirst.continuous_fderiv (by norm_num)).clm_apply
        continuous_const |>.clm_apply continuous_const

/- The local source estimate passes through aligned nonnegative mollifications. -/
end HypoellipticAleksandrov.Parabolic
