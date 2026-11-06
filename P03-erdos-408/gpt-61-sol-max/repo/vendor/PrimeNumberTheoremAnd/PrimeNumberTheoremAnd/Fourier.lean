/-
Adapted from PrimeNumberTheoremAnd by Alex Kontorovich and contributors.
Licensed under the Apache License, Version 2.0; see the upstream LICENSE.
This compatibility port retains the proven declarations used by this project.
-/
module
public import Mathlib.Tactic

public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import PrimeNumberTheoremAnd.Sobolev

@[expose] public section

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

section lemmas

section
variable {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) {c : ℂ} {u : ℝ}

@[simp] theorem F_neg     : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

include hf hg in
@[simp] theorem F_add         :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := congr_fun (VectorFourier.fourierIntegral_add Real.continuous_fourierChar continuous_inner hf hg) x

include hf hg in
@[simp] theorem F_sub         :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] theorem F_mul       :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u


end
end lemmas

theorem fourierIntegral_self_add_deriv_deriv (f : W21)  u  :
    (1 + u ^ 2) * 𝓕 (f : ℝ → ℂ) u =
      𝓕 (fun u : ℝ => (f u - (1 / (4 * π ^ 2)) * deriv^[2] f u : ℂ)) u := by
  have l1 : Integrable (fun x => (((π : ℂ) ^ 2)⁻¹ * 4⁻¹) * deriv (deriv f) x) := by
    apply Integrable.const_mul ; simpa [iteratedDeriv_succ] using f.integrable le_rfl
  have l4 : Differentiable ℝ f := f.differentiable
  have l5 : Differentiable ℝ (deriv f) := f.deriv.differentiable
  simp [f.hf, l1, add_mul, Real.fourier_deriv f.hf' l5 f.hf'', Real.fourier_deriv f.hf l4 f.hf']
  field_simp [pi_ne_zero] ; ring_nf ; simp


