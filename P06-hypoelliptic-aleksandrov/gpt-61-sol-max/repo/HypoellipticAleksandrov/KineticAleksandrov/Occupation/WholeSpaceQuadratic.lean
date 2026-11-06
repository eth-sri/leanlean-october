module

public import HypoellipticAleksandrov.Parabolic.AffineScalarCalculus
public import HypoellipticAleksandrov.Parabolic.C2ToScalarC12
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Tactic.FunProp
public import PDEFoundation.Calculus.RegularityOrder


/-! # The quadratic localization barrier for the occupation estimate -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open HypoellipticAleksandrov.Parabolic
open scoped BigOperators MatrixOrder

variable {d : ℕ}

/-- The numerator of the source quadratic supersolution. -/
def occupationQuadratic  (Lam : ℝ) (vStar : PDE.Vec d)
    (z : TimeVelocity d) : ℝ :=
  (∑ i, (z.2 i - vStar i) ^ 2) + 2 * d * Lam * (1 - z.1)

private theorem gradient_sum_sq  (vStar v : PDE.Vec d) :
    PDE.classicalGradient (fun y => ∑ i, (y i - vStar i) ^ 2) v =
      fun i => 2 * (v i - vStar i) := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun (i : Fin d) _ => ((hasFDerivAt_apply (𝕜 := ℝ) i v).sub_const (vStar i)).pow 2)
  ext i
  unfold PDE.classicalGradient
  rw [h.fderiv]
  simp [PDE.basisVec_apply]

variable (Lam : ℝ) (vStar : PDE.Vec d)

/-- The quadratic numerator is smooth. -/
theorem contDiff_occupationQuadratic   :
    ContDiff ℝ PDE.smoothOrder (occupationQuadratic Lam vStar) := by
  unfold occupationQuadratic
  fun_prop

variable (z : TimeVelocity d)

/-- Its time derivative has the backward supersolution sign. -/
theorem scalarTimeDerivative_occupationQuadratic    :
    scalarTimeDerivative (occupationQuadratic Lam vStar) z = -2 * d * Lam := by
  simp_all [scalarTimeDerivative, occupationQuadratic]

/-- Its velocity Hessian is twice the identity. -/
theorem scalarSpatialHessian_occupationQuadratic    :
    scalarSpatialHessian (occupationQuadratic Lam vStar) z =
      (2 : ℝ) • (1 : PDE.Mat d) := by
  have hg : (PDE.classicalGradient (fun w => occupationQuadratic Lam vStar (z.1, w))) =
      fun y => fun j => 2 * (y j - vStar j) := by
    funext y
    ext i
    change (fderiv ℝ (fun w : PDE.Vec d =>
      (∑ j, (w j - vStar j) ^ 2) + 2 * d * Lam * (1 - z.1)) y)
      (PDE.basisVec i) = _
    rw [fderiv_add_const]
    exact congrFun (gradient_sum_sq vStar y) i
  unfold scalarSpatialHessian
  rw [hg]

  ext i j
  rw [fderiv_pi (by
      intro j
      exact (((hasFDerivAt_apply (𝕜 := ℝ) j z.2).sub_const (vStar j)).const_mul 2).differentiableAt)]
  change (fderiv ℝ (fun y : PDE.Vec d => 2 * (y j - vStar j)) z.2)
    (PDE.basisVec i) = _

  rw [((((hasFDerivAt_apply (𝕜 := ℝ) j z.2).sub_const (vStar j)).const_mul 2).fderiv)]
  simp [PDE.basisVec_apply, Matrix.one_apply, eq_comm]

/-- Upper ellipticity makes the quadratic numerator a backward supersolution. -/
theorem scalarParabolicOperator_occupationQuadratic_le
    (B : CoefficientField d) (Lam : ℝ) (vStar : PDE.Vec d) (z : TimeVelocity d)
    (hB : B z.1 z.2 ≤ Lam • (1 : PDE.Mat d)) :
    scalarParabolicOperator B (fun _ _ => 0) (occupationQuadratic Lam vStar) z ≤ 0 := by

  have htrace := (Matrix.le_iff.mp hB).trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one] at htrace
  simp only [Fintype.card_fin, smul_eq_mul] at htrace
  have hcontract : matrixContraction (B z.1 z.2) (1 ) =
      (B z.1 z.2).trace := by
    simp [matrixContraction, Matrix.trace, Matrix.diag, Matrix.one_apply]
  unfold scalarParabolicOperator
  rw [scalarTimeDerivative_occupationQuadratic, scalarSpatialHessian_occupationQuadratic,
    matrixContraction_smul_right, hcontract]
  simp only [PDE.vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
