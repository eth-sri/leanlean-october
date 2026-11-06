/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/Hessian.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system and shortened.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.SmoothingKernel

@[expose] public section

noncomputable section
open ContDiff

set_option autoImplicit true
namespace OAI.EuclideanRamsey

notation "𝕍" k:max => (Fin k → ℝ)

section Hessian
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def hessianB (f : E → ℝ) x:=
  fderiv ℝ (fderiv ℝ f) x

lemma hessianB_eq f (x v w : E) :
    hessianB f x v w = iteratedFDeriv ℝ 2 f x ![v,w] := by simp [hessianB, iteratedFDeriv_two_apply]

lemma hessianB_linear_comp (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] F) x v w :
    hessianB (f ∘ L) x v w = hessianB f (L x) (L v) (L w) := by
  simp [hessianB_eq, L.iteratedFDeriv_comp_right hf x (by simp)]
  congr
  ext i
  fin_cases i <;> rfl

lemma hessianB_shift (hf : ContDiff ℝ ∞ f) (L : E →L[ℝ] F) x v w :
    hessianB f x (L v) (L w) = hessianB ((fun z => f (x + z)) ∘ L) 0 v w := by
  rw [hessianB_linear_comp (f := fun z => f (x + z)) (hf.comp (contDiff_const.add contDiff_id))]
  simp [hessianB_eq, iteratedFDeriv_comp_add_left' 2 x]

lemma hessianB_cms {f : E → ℝ} (hf : ContDiff ℝ ∞ f) c x v w :
    hessianB (fun y => c * f (x + y)) 0 v w = c * hessianB f x v w := by
  have := iteratedFDeriv_const_smul_apply' (a := c) (x := 0) (((hf.comp (contDiff_const.add contDiff_id)).of_le (by simp) : ContDiff ℝ 2 fun y => f (x + y)).contDiffAt)
  simp_all [hessianB_eq, Function.comp_def, iteratedFDeriv_comp_add_left']

lemma hessianB_prod {f : E → ℝ} {g : F → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) x :
    (∀ v w, hessianB (fun x => f x.1*g x.2) x (v,0) (w,0) = g x.2*hessianB f x.1 v w) ∧
    ∀ v w, hessianB (fun x => f x.1*g x.2) x (0,v) (0,w) = f x.1*hessianB g x.2 v w := by
  have h := (hf.comp contDiff_fst).mul (hg.comp contDiff_snd)
  refine ⟨fun v w => (hessianB_shift h (.inl ℝ E F) x v w).trans ?_, fun v w => (hessianB_shift h (.inr ℝ E F) x v w).trans ?_⟩ <;>
    simp [Function.comp_def, mul_comm _ (g x.2), hessianB_cms hf, hessianB_cms hg]

end Hessian

lemma pi_expand (v : 𝕍 k) : v = ∑ j, v j • Pi.single j (1:ℝ) := by
  ext
  simp [Pi.single_apply]

lemma bilinear_matrix_pushforward
    (B : 𝕍 k →L[ℝ] 𝕍 k →L[ℝ] ℝ)
    (M : Matrix (Fin k) (Fin n) ℝ) (D : 𝕄 n ℝ) :
    ∑ j, ∑ l, (M*D*M.transpose) j l * B (Pi.single j 1) (Pi.single l 1) =
      ∑ a, ∑ b, D a b * B (fun j => M j a) (fun j => M j b) := by
  conv_rhs => enter [2, a, 2, b]
              rw [pi_expand (fun j => M j a), pi_expand (fun j => M j b)]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_comm (γ := Fin k) (α := Fin n)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ?_
  simp only [ mul_left_comm, mul_assoc]

section Split
variable [AddCommGroup E] [Module ℝ E] [AddCommGroup H] [Module ℝ H]

def rightInverseSplit (U : E →ₗ[ℝ] H) (R : H →ₗ[ℝ] E)
    (hUR : U.comp R = LinearMap.id) : E ≃ₗ[ℝ] H × LinearMap.ker U where
  toFun x := (U x, ⟨x-R (U x), by simp [show U (R (U x)) = U x from LinearMap.congr_fun hUR (U x)]⟩)
  invFun v := R v.1 + v.2
  left_inv x := by simp
  right_inv v := by
    ext <;> simp [show U (R v.1) = v.1 from LinearMap.congr_fun hUR v.1]
  map_add' v w := by ext <;> simp
                     abel
  map_smul' c x := by ext <;> simp [ smul_sub]
