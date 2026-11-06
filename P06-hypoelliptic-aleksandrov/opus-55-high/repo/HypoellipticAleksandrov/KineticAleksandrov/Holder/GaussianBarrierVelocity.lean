module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.QuadraticCalculusVelocity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierFinite
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic

/-! # Native velocity derivatives of an exponential quadratic -/

@[expose] public section


namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Parabolic

variable {d : ℕ} {g : PDE.Vec d → ℝ}

/-- Differentiating a negative exponential gives its native classical gradient. -/
theorem classicalGradient_exp_neg  {W : PDE.Vec d}
    (hg : DifferentiableAt ℝ g W) :
    PDE.classicalGradient (fun V => Real.exp (-g V)) W =
      (-Real.exp (-g W)) • PDE.classicalGradient g W := by
  aesop

/-- The exponential Hessian includes both the gradient square and the quadratic Hessian. -/
theorem sliceHessian_exp_neg 
    (hg : ContDiff ℝ 2 g) (W : PDE.Vec d) (i j : Fin d) :
    sliceHessian (fun V => Real.exp (-g V)) W i j = Real.exp (-g W) *
      (PDE.classicalGradient g W i * PDE.classicalGradient g W j - sliceHessian g W i j) := by
  have hgrad : (fun V => PDE.classicalGradient (fun U => Real.exp (-g U)) V) =
      (fun V => (-Real.exp (-g V)) • PDE.classicalGradient g V) := by
    funext V
    exact classicalGradient_exp_neg (hg.differentiable (by norm_num) V)
  have hd := hg.differentiable (by norm_num) W
  have hfd : DifferentiableAt ℝ (fderiv ℝ g) W :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) W
  have hgj : HasFDerivAt (fun V => PDE.classicalGradient g V j)
      (fderiv ℝ (fun V => PDE.classicalGradient g V j) W) W :=
    (hfd.clm_apply (differentiableAt_const _)).hasFDerivAt
  have hp := (hd.hasFDerivAt.neg.exp.neg).mul hgj
  have heq : (fun V => ((-Real.exp (-g V)) • PDE.classicalGradient g V) j) =
      (fun V => (-Real.exp (-g V)) * PDE.classicalGradient g V j) := by
    rfl
  unfold sliceHessian
  rw [hgrad]
  have hgjval : fderiv ℝ (fun V => PDE.classicalGradient g V j) W (PDE.basisVec i) =
      (fderiv ℝ (fun V => PDE.classicalGradient g V) W (PDE.basisVec i)) j := (congrArg (fun L => L (PDE.basisVec i))
      ((hasFDerivAt_apply (𝕜 := ℝ) j _).comp W
        (show DifferentiableAt ℝ (PDE.classicalGradient g) W from by
          exact differentiableAt_pi.mpr (fun k =>
            hfd.clm_apply (differentiableAt_const _))).hasFDerivAt).fderiv)
  have hG : DifferentiableAt ℝ (fun V => (-Real.exp (-g V)) • PDE.classicalGradient g V) W :=
    (hd.neg.exp.neg).smul (differentiableAt_pi.mpr (fun k =>
      hfd.clm_apply (differentiableAt_const _)))
  have hcomp := (hasFDerivAt_apply (𝕜 := ℝ) j
    _).comp W hG.hasFDerivAt
  have hproj : (fderiv ℝ (fun V => (-Real.exp (-g V)) • PDE.classicalGradient g V) W
      (PDE.basisVec i)) j =
      fderiv ℝ (fun V => ((-Real.exp (-g V)) • PDE.classicalGradient g V) j) W
        (PDE.basisVec i) := by
    have hder := hcomp.fderiv
    simp only [Function.comp_def] at hder
    simp_all
  have hpder := hp.fderiv
  change fderiv ℝ (fun V => -Real.exp (-g V) * PDE.classicalGradient g V j) W = _
    at hpder
  simp only [Pi.neg_apply] at hpder
  rw [hproj, heq, hpder]
  simp only [add_apply, smul_apply,
    neg_apply]
  rw [hgjval]
  simp only [PDE.classicalGradient]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Holder
