module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ConeSupportComparison
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.FDeriv.Comp
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierCollar
public import PDEFoundation.Calculus.RegularityOrder


/-! # Smooth bounded probes of affine physical transport coordinates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Parabolic

variable {d : ℕ}

/-- Continuous linear dot product with a fixed raw Euclidean vector. -/
def coneDotLinear  (e : PDE.Vec d) : PDE.Vec d →L[ℝ] ℝ :=
  ∑ i, e i • ContinuousLinearMap.proj i

/-- The dot-product functional uses exactly the finite Euclidean sum. -/
theorem coneDotLinear_apply  (e x : PDE.Vec d) :
    coneDotLinear e x = PDE.vecDot e x := by
  simp_all [coneDotLinear, PDE.vecDot]

variable (α : ℝ) (e : PDE.Vec d) (γ : ℝ)

/-- An affine physical transport coordinate. -/
def coneCoordinate   (P : KineticPoint d) : ℝ :=
  α * P.time + PDE.vecDot e P.position + γ

/-- The bounded transition of an affine transport coordinate is globally smooth. -/
theorem coneProbe_smooth   :
    ContDiff ℝ PDE.smoothOrder ((expNegInvGlue ∘ coneCoordinate α e γ) ∘
      (KineticPoint.equivProd d).symm) := by
  apply expNegInvGlue.contDiff.comp
  change ContDiff ℝ PDE.smoothOrder (fun x : ℝ × PDE.Vec d × PDE.Vec d =>
    α * x.1 + PDE.vecDot e x.2.1 + γ)
  unfold PDE.vecDot
  fun_prop

/-- The transport probe has zero velocity Hessian and the exact directional operator. -/
theorem coneProbe_operator  (B : CoefficientField d)
    (α : ℝ) (e : PDE.Vec d) (γ : ℝ) (P : KineticPoint d) :
    forwardKineticOperator (ofTimeVelocityCoefficient B)
      (expNegInvGlue ∘ coneCoordinate α e γ) P =
      (α + PDE.vecDot P.velocity e) *
        deriv expNegInvGlue (coneCoordinate α e γ P) := by
  let χ := expNegInvGlue
  have hd (x : ℝ) : DifferentiableAt ℝ χ x :=
    (expNegInvGlue.contDiff : ContDiff ℝ PDE.smoothOrder expNegInvGlue).differentiable
      (by simp) x
  have ht : kineticTimeDerivative (χ ∘ coneCoordinate α e γ) P =
      deriv χ (coneCoordinate α e γ P) * α := by
    have hh := (hd _).hasDerivAt.comp P.time
      ((((hasDerivAt_id P.time).const_mul α).add_const (PDE.vecDot e P.position)).add_const γ)
    simpa only [kineticTimeDerivative, coneCoordinate, Function.comp_apply, id_eq, mul_one]
      using! hh.deriv
  have hx : kineticPositionGradient (χ ∘ coneCoordinate α e γ) P =
      (deriv χ (coneCoordinate α e γ P)) • e := by
    have hh₀ := (hd (α * P.time + coneDotLinear e P.position + γ)).hasDerivAt
      |>.comp_hasFDerivAt P.position
        (((coneDotLinear e).hasFDerivAt.const_add (α * P.time)).add_const γ)
    have hh : HasFDerivAt
        (χ ∘ (fun x => α * P.time + coneDotLinear e x + γ))
        (deriv χ (coneCoordinate α e γ P) • coneDotLinear e) P.position := by
      simpa only [coneCoordinate, coneDotLinear_apply] using! hh₀
    have heq : (fun x  => χ (α * P.time + PDE.vecDot e x + γ)) =
        χ ∘ (fun x => α * P.time + coneDotLinear e x + γ) := by
      funext x
      rw [Function.comp_apply, coneDotLinear_apply]
    funext i
    simp only [kineticPositionGradient, PDE.classicalGradient_apply]
    change fderiv ℝ (fun x  => χ (α * P.time + PDE.vecDot e x + γ))
      P.position (PDE.basisVec i) = _
    rw [heq, hh.fderiv]
    simp [coneDotLinear, PDE.basisVec, Pi.smul_apply, Pi.single_apply]
  have hv : kineticVelocityHessian (χ ∘ coneCoordinate α e γ) P = 0 := by
    unfold kineticVelocityHessian
    change (fun i j => (fderiv ℝ ((PDE.classicalGradient (fun _ : PDE.Vec d => χ (coneCoordinate α e γ P))))
        P.velocity (PDE.basisVec i)) j) = 0
    have hg : ((PDE.classicalGradient (fun _ : PDE.Vec d => χ (coneCoordinate α e γ P)))) =
        fun _ => 0 := funext ((classicalGradient_const _))
    rw [hg]
    have hf : fderiv ℝ (fun _ : PDE.Vec d => (0 : PDE.Vec d)) P.velocity = 0 :=
      congrFun (fderiv_const (0 : PDE.Vec d)) P.velocity
    rw [hf]
    rfl

  rw [forwardKineticOperator_apply, ht, hx, hv]
  simp only [matrixContraction, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  simp only [PDE.vecDot, Pi.smul_apply, smul_eq_mul]
  have he (i : Fin d) : P.velocity i * (deriv χ (coneCoordinate α e γ P) * e i) =
      (P.velocity i * e i) * deriv χ (coneCoordinate α e γ P) := by ring
  simp_rw [he]
  rw [← Finset.sum_mul]
  dsimp only [χ]
  ring

/-- The smooth transition is nonnegative and at most one. -/
theorem coneProbe_transition_bound (x : ℝ) :
    0 ≤ expNegInvGlue x ∧ expNegInvGlue x ≤ 1 := by
  refine ⟨expNegInvGlue.nonneg x, ?_⟩
  by_cases hx : x ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos hx]
    exact zero_le_one
  · rw [expNegInvGlue, ite_eq_right hx]
    exact Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (inv_nonneg.mpr (not_le.mp hx).le))

/-- Nonpositive transport speed makes the bounded probe a supersolution. -/
theorem coneProbe_operator_nonpos {d : ℕ} (B : CoefficientField d)
    (α : ℝ) (e : PDE.Vec d) (γ : ℝ) (P : KineticPoint d)
    (hdir : α + PDE.vecDot P.velocity e ≤ 0) :
    forwardKineticOperator (ofTimeVelocityCoefficient B)
      (expNegInvGlue ∘ coneCoordinate α e γ) P ≤ 0 := by
  rw [coneProbe_operator]

  exact mul_nonpos_of_nonpos_of_nonneg hdir expNegInvGlue.monotone.deriv_nonneg

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
