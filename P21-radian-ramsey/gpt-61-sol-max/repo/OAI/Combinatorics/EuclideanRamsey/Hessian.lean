/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/Hessian.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`); subsequently
refactored and proof-compressed while preserving the main results.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.SmoothingKernel

@[expose] public section

open scoped ContDiff

namespace OAI.EuclideanRamsey


noncomputable section




section Hessian
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def hessianB (f : E → ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fun y => fderiv ℝ f y) x

lemma hessianB_eq (f : E → ℝ) (x v w : E) :
    hessianB f x v w = iteratedFDeriv ℝ 2 f x ![v,w] := by
  simp [hessianB,iteratedFDeriv_two_apply]

lemma hessianB_linear_comp {f : F → ℝ} (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] F) (x v w : E) :
    hessianB (f ∘ L) x v w = hessianB f (L x) (L v) (L w) := by
  simp only [hessianB_eq, L.iteratedFDeriv_comp_right hf x (by simp),
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

lemma hessianB_prod_horizontal {f : E → ℝ} {g : F → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : E × F) (v w : E) :
    hessianB (fun x : E × F => f x.1*g x.2) x (v,0) (w,0) =
      g x.2*hessianB f x.1 v w := by
  let φ : E×F → ℝ := fun y => f y.1*g y.2
  have hφ : ContDiff ℝ ∞ φ := (hf.comp contDiff_fst).mul (hg.comp contDiff_snd)
  have h := hessianB_linear_comp
    (hφ.comp (contDiff_const.add contDiff_id) : ContDiff ℝ ∞ (fun y => φ ((0,x.2)+y)))
    (ContinuousLinearMap.inl ℝ E F) x.1 v w
  simp only [hessianB_eq,Function.comp_def,iteratedFDeriv_comp_add_left] at h
  simp [φ, ← smul_eq_mul,
    iteratedFDeriv_smul_const_apply (hf.of_le (by simp)).contDiffAt] at h
  simp_all [hessianB_eq] <;> nlinarith


lemma hessianB_prod_vertical {f : E → ℝ} {g : F → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : E × F) (v w : F) :
    hessianB (fun x : E × F => f x.1*g x.2) x (0,v) (0,w) =
      f x.1*hessianB g x.2 v w := by
  simpa [Function.comp_def, mul_comm] using
    (hessianB_linear_comp ((hg.comp contDiff_fst).mul (hf.comp contDiff_snd))
      (ContinuousLinearEquiv.prodComm ℝ E F).toContinuousLinearMap x (0,v) (0,w)).trans
        (hessianB_prod_horizontal hg hf (x.2,x.1) v w)

lemma hessianB_compact {f : E → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (hessianB f) := (hf.fderiv ℝ).fderiv ℝ

end Hessian


lemma bilinear_matrix_pushforward {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (B : (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ)
    (M : Matrix ι κ ℝ) (D : Matrix κ κ ℝ) :
    ∑ j, ∑ l, (M*D*M.transpose) j l * B (Pi.single j 1) (Pi.single l 1) =
      ∑ a, ∑ b, D a b * B (fun j => M j a) (fun j => M j b) := by
  let A := B.toBilinForm.toMatrix'
  have h := Matrix.trace_mul_cycle M D (M.transpose * A.transpose)
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm _ D] at h
  have he : M.transpose * A.transpose * M =
      (B.toBilinForm.comp M.toLin' M.toLin').toMatrix'.transpose := by
    simp [LinearMap.BilinForm.toMatrix'_comp, Matrix.transpose_mul, A, Matrix.mul_assoc]
  rw [he] at h
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
  LinearMap.BilinForm.toMatrix'_apply, ContinuousLinearMap.toBilinForm_apply, LinearMap.BilinForm.comp_apply,
  Matrix.toLin'_apply, Matrix.mulVec_single, MulOpposite.op_one, Matrix.col, one_smul, A] at h
  exact h



end

end OAI.EuclideanRamsey
