/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationHermitianUniqueness
public import DOZZ.Hypergeom.ClassificationWirtingerBar
public import DOZZ.Hypergeom.ClassificationWirtingerC2
import Mathlib.Analysis.Calculus.FDeriv.Star

/-! First Wirtinger derivatives and real `C²` regularity of a constant Hermitian tensor. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter
open scoped Topology

/-- A constant-coefficient sesquilinear tensor in two holomorphic functions. -/
noncomputable def hermitianQuadraticTensor (f g : ℂ → ℂ) (A B C D : ℂ) : ℂ → ℂ :=
  fun z => A * f z * star (f z) + B * f z * star (g z) +
    C * g z * star (f z) + D * g z * star (g z)

/-- The `∂z` expression of a constant sesquilinear tensor. -/
noncomputable def hermitianQuadraticTensorZ (f g : ℂ → ℂ) (A B C D : ℂ) : ℂ → ℂ :=
  fun z => A * deriv f z * star (f z) + B * deriv f z * star (g z) +
    C * deriv g z * star (f z) + D * deriv g z * star (g z)

private theorem wirtingerBar_star_eq_star_deriv_at {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z) :
    wirtingerBar (fun w => star (g w)) z = star (deriv g z) := by
  apply wirtingerBar_eq_star_deriv_of_star_differentiableAt hg
  funext w
  simp

section
variable (k : ℂ) {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z)
include hf hg

private theorem wirtingerZ_const_mul_star_term :
    wirtingerZ (fun w => k * f w * star (g w)) z =
      k * deriv f z * star (g z) := by
  have hKf : DifferentiableAt ℂ (fun w => k * f w) z :=
    (differentiableAt_const k).mul hf
  have h := wirtingerZ_mul_star_of_differentiableAt hKf hg
  change wirtingerZ (fun w => (k * f w) * star (g w)) z = _
  rw [h, deriv_const_mul_field]
  ring

private theorem wirtingerBar_const_mul_star_term :
    wirtingerBar (fun w => k * f w * star (g w)) z =
      k * f z * star (deriv g z) := by
  have hKf : DifferentiableAt ℂ (fun w => k * f w) z :=
    (differentiableAt_const k).mul hf
  have h := wirtingerBar_mul (hKf.restrictScalars ℝ)
    ((hg.restrictScalars ℝ).star)
  change wirtingerBar (fun w => (k * f w) * star (g w)) z = _
  rw [h, wirtingerBar_eq_zero_of_differentiableAt hKf,
    wirtingerBar_star_eq_star_deriv_at hg]
  ring

end

/-- The same sesquilinear combination for possibly different left and right bases. -/
noncomputable def sesquilinearTensor (f g j k : ℂ → ℂ) (A B C D : ℂ) (z : ℂ) : ℂ :=
  A * f z * star (j z) + B * f z * star (k z) + C * g z * star (j z) + D * g z * star (k z)

/-- The conjugate derivative acts on the right basis, independently of the left basis. -/
theorem sesquilinearTensor_wirtingerBar {f g j k : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z)
    (hj : DifferentiableAt ℂ j z) (hk : DifferentiableAt ℂ k z) (A B C D : ℂ) :
    wirtingerBar (sesquilinearTensor f g j k A B C D) z =
      sesquilinearTensor f g (deriv j) (deriv k) A B C D z := by
  unfold sesquilinearTensor
  simp (disch := fun_prop) only [wirtingerBar_add,
    wirtingerBar_const_mul_star_term]

section
variable {f g : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U) (A B C D : ℂ)
  {z : ℂ} (hz : z ∈ U)
include U hf hg hz

/-- First `∂z` derivative of the constant Hermitian tensor. -/
theorem hermitianQuadraticTensor_wirtingerZ :
    wirtingerZ (hermitianQuadraticTensor f g A B C D) z =
      hermitianQuadraticTensorZ f g A B C D z := by
  have hfAt := (hf z hz).differentiableAt
  have hgAt := (hg z hz).differentiableAt
  unfold hermitianQuadraticTensor hermitianQuadraticTensorZ
  simp (disch := fun_prop) only [wirtingerZ_add, wirtingerZ_const_mul_star_term]

/-- First `∂bar` derivative of the constant Hermitian tensor. -/
theorem hermitianQuadraticTensor_wirtingerBar :
    wirtingerBar (hermitianQuadraticTensor f g A B C D) z =
      A * f z * star (deriv f z) + B * f z * star (deriv g z) +
      C * g z * star (deriv f z) + D * g z * star (deriv g z) :=
  sesquilinearTensor_wirtingerBar (hf z hz).differentiableAt (hg z hz).differentiableAt
    (hf z hz).differentiableAt (hg z hz).differentiableAt A B C D

/-- A constant Hermitian tensor is twice continuously real-differentiable wherever its two
holomorphic factors are analytic. -/
theorem hermitianQuadraticTensor_contDiffAt_two :
    ContDiffAt ℝ 2 (hermitianQuadraticTensor f g A B C D) z := by
  have hfAt : ContDiffAt ℝ 2 f z := (hf z hz).contDiffAt.restrict_scalars ℝ
  have hgAt : ContDiffAt ℝ 2 g z := (hg z hz).contDiffAt.restrict_scalars ℝ
  have hs {f : ℂ → ℂ} (hf : ContDiffAt ℝ 2 f z) : ContDiffAt ℝ 2 (fun w => star (f w)) z :=
    Complex.conjCLE.contDiff.contDiffAt.comp z hf
  have := hs hfAt
  have := hs hgAt
  unfold hermitianQuadraticTensor
  fun_prop

end

end DOZZ.Proofs
