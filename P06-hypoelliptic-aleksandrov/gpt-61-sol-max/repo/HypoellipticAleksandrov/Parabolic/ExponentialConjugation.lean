module

public import HypoellipticAleksandrov.Parabolic.LocalClassical
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring



/-!
# Exponential time conjugation for the forward parabolic operator

Multiplication by `exp (rho * (t - tBase))` removes a zeroth-order term from
the project-sign operator `∂t - A : Dv²`.  The identities are local in the
scalar function and impose no sign condition on `rho`, coefficient
regularity, ellipticity, or parabolic estimate.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

open Filter
open scoped Topology

variable {d : ℕ}

variable (rho tBase : ℝ)

/-- The positive exponential weight based at the time `tBase`. -/
def exponentialTimeWeight   (z : TimeVelocity d) : ℝ :=
  Real.exp (rho * (z.1 - tBase))

/-- The exponential time conjugate of a scalar function. -/
def exponentialConjugate
    (w : TimeVelocity d → ℝ) (z : TimeVelocity d) : ℝ :=
  exponentialTimeWeight rho tBase z * w z

/-- Evaluation of the exponential time weight. -/
@[simp] theorem exponentialTimeWeight_apply
    (z : TimeVelocity d) :
    exponentialTimeWeight rho tBase z = Real.exp (rho * (z.1 - tBase)) :=
  rfl

/-- Evaluation of the exponential time conjugate. -/
@[simp] theorem exponentialConjugate_apply
    (w : TimeVelocity d → ℝ) (z : TimeVelocity d) :
    exponentialConjugate rho tBase w z = exponentialTimeWeight rho tBase z * w z :=
  rfl

/-- The exponential time weight is strictly positive at every point. -/
theorem exponentialTimeWeight_pos   (z : TimeVelocity d) :
    0 < exponentialTimeWeight rho tBase z :=
  Real.exp_pos _

/-- The exponential time weight is globally smooth. -/
theorem contDiff_exponentialTimeWeight   :
    ContDiff ℝ ⊤ (exponentialTimeWeight (d := d) rho tBase) := by
  unfold exponentialTimeWeight
  fun_prop

/-- Exponential conjugation preserves local `C²` regularity. -/
theorem contDiffOn_exponentialConjugate  {U : HypoellipticAleksandrov.Parabolic.Region d}
    {rho tBase : ℝ} {w : TimeVelocity d → ℝ}
    (hw : ContDiffOn ℝ 2 w U) :
    ContDiffOn ℝ 2 (exponentialConjugate rho tBase w) U := (((contDiff_exponentialTimeWeight rho tBase).of_le (by norm_num)).contDiffOn).mul hw

private theorem fderiv_timeCoordinate_apply
    (z direction : TimeVelocity d) :
    fderiv ℝ (fun y : TimeVelocity d => y.1) z direction = direction.1 := by
  rw [(hasFDerivAt_fst (𝕜 := ℝ) (p := z)).fderiv]
  rfl

private theorem fderiv_exponentialTimeWeight_apply  (rho tBase : ℝ)
    (z direction : TimeVelocity d) :
    fderiv ℝ (exponentialTimeWeight rho tBase) z direction =
      exponentialTimeWeight rho tBase z * (rho * direction.1) := by
  unfold exponentialTimeWeight
  rw [fderiv_exp (by fun_prop)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_const_mul (by fun_prop) rho]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_fun_sub (by fun_prop) (by fun_prop)]
  simp only [fderiv_timeCoordinate_apply,
    fderiv_const_apply, sub_zero]

private theorem fderiv_fderiv_apply_eq_fderiv_eval
    {w : TimeVelocity d → ℝ} {z direction₁ direction₂ : TimeVelocity d}
    (hw : ContDiffAt ℝ 2 w z) :
    fderiv ℝ (fderiv ℝ w) z direction₁ direction₂ =
      fderiv ℝ (fun y => fderiv ℝ w y direction₂) z direction₁ := by

  have hEval :
      fderiv ℝ (fun y => fderiv ℝ w y direction₂) z =
        (fderiv ℝ (fderiv ℝ w) z).flip direction₂ := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using
      ((((hw.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt.clm_apply
        (hasFDerivAt_const direction₂ z)).fderiv)
  simp_all

private theorem fderiv_fderiv_exponentialTimeWeight_apply
    (rho tBase : ℝ) (z direction₁ direction₂ : TimeVelocity d) :
    fderiv ℝ (fderiv ℝ (exponentialTimeWeight rho tBase)) z direction₁ direction₂ =
      exponentialTimeWeight rho tBase z * rho ^ 2 * direction₁.1 * direction₂.1 := by
  let e : TimeVelocity d → ℝ := exponentialTimeWeight rho tBase

  calc
    fderiv ℝ (fderiv ℝ e) z direction₁ direction₂ =
        fderiv ℝ (fun y => fderiv ℝ e y direction₂) z direction₁ :=
      fderiv_fderiv_apply_eq_fderiv_eval ((contDiff_exponentialTimeWeight rho tBase).of_le (by norm_num)).contDiffAt
    _ = fderiv ℝ (fun y => e y * (rho * direction₂.1)) z direction₁ := by
      congr 2
      funext y
      exact fderiv_exponentialTimeWeight_apply rho tBase y direction₂
    _ = e z * rho ^ 2 * direction₁.1 * direction₂.1 := by
      rw [fderiv_mul_const ((contDiff_exponentialTimeWeight rho tBase).differentiable (by norm_num) z)
        (rho * direction₂.1)]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [fderiv_exponentialTimeWeight_apply]
      ring

section
variable {rho tBase : ℝ} {w : TimeVelocity d → ℝ} {z : TimeVelocity d} (hw : ContDiffAt ℝ 2 w z)

include hw
/-- The exact time derivative after exponential time conjugation. -/
theorem timeDerivative_exponentialConjugate   :
    timeDerivative (exponentialConjugate rho tBase w) z =
      exponentialTimeWeight rho tBase z * (timeDerivative w z + rho * w z) := by


  unfold timeDerivative exponentialConjugate
  rw [fderiv_fun_mul ((contDiff_exponentialTimeWeight rho tBase).differentiable (by norm_num) z) (hw.differentiableAt (by norm_num))]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rw [fderiv_exponentialTimeWeight_apply]
  simp only [mul_add]
  ring

/-- The exact velocity Hessian after exponential time conjugation. -/
theorem velocityHessian_exponentialConjugate   :
    velocityHessian (exponentialConjugate rho tBase w) z =
      exponentialTimeWeight rho tBase z • velocityHessian w z := by
  let e : TimeVelocity d → ℝ := exponentialTimeWeight rho tBase
  let g  := exponentialConjugate rho tBase w
  have he : ContDiff ℝ 2 e :=
    (contDiff_exponentialTimeWeight rho tBase).of_le (by norm_num)
  have heDiff : DifferentiableAt ℝ e z := he.differentiable (by norm_num) z
  have hwDiff : DifferentiableAt ℝ w z := hw.differentiableAt (by norm_num)
  have hDwe : DifferentiableAt ℝ (fderiv ℝ w) z :=
    (hw.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDe : DifferentiableAt ℝ (fderiv ℝ e) z :=
    (he.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  ext i j
  let direction₁ : TimeVelocity d := (0, Pi.single i 1)
  let direction₂ : TimeVelocity d := (0, Pi.single j 1)


  unfold velocityHessian
  change fderiv ℝ (fderiv ℝ g) z direction₁ direction₂ =
    (e z • velocityHessian w z) i j
  calc
    fderiv ℝ (fderiv ℝ g) z direction₁ direction₂ =
    fderiv ℝ (fun y => fderiv ℝ g y direction₂) z direction₁ :=
      fderiv_fderiv_apply_eq_fderiv_eval (he.contDiffAt.mul hw)
    _ = fderiv ℝ
        (fun y => e y * fderiv ℝ w y direction₂ + w y * fderiv ℝ e y direction₂)
          z direction₁ := congrArg (fun L : TimeVelocity d →L[ℝ] ℝ => L direction₁)
        ((show (fun y => fderiv ℝ g y direction₂) =ᶠ[𝓝 z]
        fun y => e y * fderiv ℝ w y direction₂ + w y * fderiv ℝ e y direction₂ by
            filter_upwards [(hw.eventually (by norm_num))] with y hy


            change fderiv ℝ (fun x => e x * w x) y direction₂ =
              e y * fderiv ℝ w y direction₂ + w y * fderiv ℝ e y direction₂
            rw [fderiv_fun_mul (he.differentiable (by norm_num) y) (hy.differentiableAt (by norm_num))]
            simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
              smul_eq_mul]).fderiv_eq )
    _ = e z * fderiv ℝ (fderiv ℝ w) z direction₁ direction₂ +
          fderiv ℝ e z direction₁ * fderiv ℝ w z direction₂ +
          w z * fderiv ℝ (fderiv ℝ e) z direction₁ direction₂ +
          fderiv ℝ w z direction₁ * fderiv ℝ e z direction₂ := by
      have hEvalW : DifferentiableAt ℝ
          (fun y => fderiv ℝ w y direction₂) z :=
        hDwe.clm_apply (hasFDerivAt_const direction₂ z).differentiableAt
      have hEvalE : DifferentiableAt ℝ
          (fun y => fderiv ℝ e y direction₂) z :=
        hDe.clm_apply (hasFDerivAt_const direction₂ z).differentiableAt
      let first  := fun y => e y * fderiv ℝ w y direction₂
      let second  := fun y => w y * fderiv ℝ e y direction₂
      have hfirst : DifferentiableAt ℝ first z := heDiff.mul hEvalW
      have hsecond : DifferentiableAt ℝ second z := hwDiff.mul hEvalE
      calc
        fderiv ℝ
            (fun y => e y * fderiv ℝ w y direction₂ + w y * fderiv ℝ e y direction₂)
            z direction₁ =
            fderiv ℝ first z direction₁ + fderiv ℝ second z direction₁ := by
          change fderiv ℝ (first + second) z direction₁ = _
          rw [fderiv_add hfirst hsecond]
          rfl
        _ = e z * fderiv ℝ (fderiv ℝ w) z direction₁ direction₂ +
            fderiv ℝ e z direction₁ * fderiv ℝ w z direction₂ +
            w z * fderiv ℝ (fderiv ℝ e) z direction₁ direction₂ +
            fderiv ℝ w z direction₁ * fderiv ℝ e z direction₂ := by
          dsimp only [first, second]
          rw [fderiv_fun_mul heDiff hEvalW,
            fderiv_fun_mul hwDiff hEvalE]
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
            smul_eq_mul]
          rw [← fderiv_fderiv_apply_eq_fderiv_eval hw,
            ← fderiv_fderiv_apply_eq_fderiv_eval he.contDiffAt,
            fderiv_exponentialTimeWeight_apply,
            fderiv_exponentialTimeWeight_apply,
            fderiv_fderiv_exponentialTimeWeight_apply]
          ring
    _ = (e z • velocityHessian w z) i j := by
      dsimp only [direction₁, direction₂]
      rw [fderiv_exponentialTimeWeight_apply rho tBase z,
        fderiv_exponentialTimeWeight_apply rho tBase z,
        fderiv_fderiv_exponentialTimeWeight_apply rho tBase z]
      simp only [mul_zero, zero_mul, add_zero,
        Matrix.smul_apply, smul_eq_mul, velocityHessian]
end


/-- The exact project-sign operator identity after exponential time
conjugation. -/
theorem parabolicOperator_exponentialConjugate  (A : CoefficientField d)
    {rho tBase : ℝ} {w : TimeVelocity d → ℝ} {z : TimeVelocity d}
    (hw : ContDiffAt ℝ 2 w z) :
    parabolicOperator A (exponentialConjugate rho tBase w) z =
      exponentialTimeWeight rho tBase z * (parabolicOperator A w z + rho * w z) := by
  simp_all [timeDerivative_exponentialConjugate, velocityHessian_exponentialConjugate] <;> ring

/-- At a point, exponential conjugation preserves a nonpositive scalar sign. -/
theorem exponentialConjugate_nonpos_iff  (rho tBase : ℝ)
    (w : TimeVelocity d → ℝ) (z : TimeVelocity d) :
    exponentialConjugate rho tBase w z ≤ 0 ↔ w z ≤ 0 := by
  rw [exponentialConjugate_apply]
  constructor
  · intro h
    exact nonpos_of_mul_nonpos_right h (exponentialTimeWeight_pos rho tBase z)
  · intro hw
    exact mul_nonpos_of_nonneg_of_nonpos (exponentialTimeWeight_pos rho tBase z).le hw

end

end HypoellipticAleksandrov.Parabolic
