module

public import HypoellipticAleksandrov.Parabolic.AffineScalarCalculus
public import HypoellipticAleksandrov.Parabolic.C2ToScalarC12
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Tactic.FunProp

/-! # The quadratic localization barrier for the occupation estimate -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open HypoellipticAleksandrov.Parabolic
open scoped BigOperators MatrixOrder

/- The numerator of the source quadratic supersolution. -/
def occupationQuadratic {d } (Lam : ℝ) (vStar : PDE.Vec d)
    (z : TimeVelocity d) : ℝ :=
  (∑ i, (z.2 i - vStar i) ^ 2) + 2 * d * Lam * (1 - z.1)

private theorem gradient_sum_sq {d } (vStar v : PDE.Vec d) :
    PDE.classicalGradient (fun y => ∑ i, (y i - vStar i) ^ 2) v =
      fun i => 2 * (v i - vStar i) := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun (i : Fin d) _ => ((hasFDerivAt_apply (𝕜 := ℝ) i v).sub_const (vStar i)).pow 2)
  ext i
  unfold PDE.classicalGradient
  rw [h.fderiv]
  simp [PDE.basisVec_apply]

/- The quadratic numerator is smooth. -/
theorem contDiff_occupationQuadratic {d } (Lam : ℝ) (vStar : PDE.Vec d) :
    ContDiff ℝ (⊤ : ℕ∞) (occupationQuadratic Lam vStar) := by
  unfold occupationQuadratic
  fun_prop

/- Its time derivative has the backward supersolution sign. -/
theorem scalarTimeDerivative_occupationQuadratic {d } (Lam : ℝ)
    (vStar : PDE.Vec d) (z : TimeVelocity d) :
    scalarTimeDerivative (occupationQuadratic Lam vStar) z = -2 * d * Lam := by
  unfold scalarTimeDerivative occupationQuadratic
  have h' := (((hasDerivAt_id z.1).const_sub 1).const_mul (2 * d * Lam)).const_add (∑ i, (z.2 i - vStar i) ^ 2)
  simpa only [mul_neg, mul_one, neg_mul, id_eq] using h'.deriv

/- Its velocity Hessian is twice the identity. -/
theorem scalarSpatialHessian_occupationQuadratic {d } (Lam : ℝ)
    (vStar : PDE.Vec d) (z : TimeVelocity d) :
    scalarSpatialHessian (occupationQuadratic Lam vStar) z =
      (2 : ℝ) • (1 : PDE.Mat d) := by
  have hg : (fun y : PDE.Vec d =>
      PDE.classicalGradient (fun w => occupationQuadratic Lam vStar (z.1, w)) y) =
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
  have hdiff : ∀ j : Fin d,
      DifferentiableAt ℝ (fun y : PDE.Vec d => 2 * (y j - vStar j)) z.2 := by
    intro j
    exact (((hasFDerivAt_apply (𝕜 := ℝ) j z.2).sub_const (vStar j)).const_mul 2).differentiableAt
  ext i j
  rw [fderiv_pi hdiff]
  change (fderiv ℝ (fun y : PDE.Vec d => 2 * (y j - vStar j)) z.2)
    (PDE.basisVec i) = _
  have h := (((hasFDerivAt_apply (𝕜 := ℝ) j z.2).sub_const (vStar j)).const_mul 2).fderiv
  rw [h]
  simp [PDE.basisVec_apply, Matrix.one_apply, eq_comm]

/- Upper ellipticity makes the quadratic numerator a backward supersolution. -/
end HypoellipticAleksandrov.KineticAleksandrov.Occupation
