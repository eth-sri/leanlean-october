/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationHermitianJets

/-! The mixed Wirtinger jet of a constant Hermitian tensor. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter
open scoped Topology

section
variable {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
  (hg : AnalyticOnNhd ℂ g U)
include hU hf hg

/-- The mixed conjugate Wirtinger derivative of a Hermitian tensor differentiates both
holomorphic factors. -/
theorem hermitianQuadraticTensor_mixed
    (A B C D : ℂ) {z : ℂ} (hz : z ∈ U) :
    wirtingerBar (fun w => wirtingerZ (hermitianQuadraticTensor f g A B C D) w) z =
      A * deriv f z * star (deriv f z) + B * deriv f z * star (deriv g z) +
        C * deriv g z * star (deriv f z) + D * deriv g z * star (deriv g z) := by
  have hfirst : (fun w => wirtingerZ (hermitianQuadraticTensor f g A B C D) w) =ᶠ[𝓝 z]
      hermitianQuadraticTensorZ f g A B C D :=
    (show ∀ᶠ w in 𝓝 z, w ∈ U from hU.mem_nhds hz).mono
      fun w hw => hermitianQuadraticTensor_wirtingerZ hf hg A B C D hw
  rw [wirtingerBar_congr_of_eventuallyEq hfirst]
  exact sesquilinearTensor_wirtingerBar (hf.deriv z hz).differentiableAt
    (hg.deriv z hz).differentiableAt (hf z hz).differentiableAt (hg z hz).differentiableAt A B C D

/-- Equality of Hermitian tensors on an open set determines all four coefficients whenever the
analytic basis has nonzero Wronskian. The value, both first Wirtinger derivatives, and the mixed
jet recover the coefficient matrix. -/
theorem hermitianTensor_coefficients_eq_of_eqOn
    (A B C D A' B' C' D' : ℂ) {z : ℂ} (hz : z ∈ U)
    (hW : f z * deriv g z - deriv f z * g z ≠ 0)
    (hEq : ∀ w ∈ U,
      hermitianQuadraticTensor f g A B C D w =
        hermitianQuadraticTensor f g A' B' C' D' w) :
    A = A' ∧ B = B' ∧ C = C' ∧ D = D' := by
  have hn : hermitianQuadraticTensor f g A B C D =ᶠ[𝓝 z]
      hermitianQuadraticTensor f g A' B' C' D' := (show ∀ᶠ w in 𝓝 z, w ∈ U from hU.mem_nhds hz).mono hEq
  have hZ := wirtingerZ_congr_of_eventuallyEq hn
  have hB := wirtingerBar_congr_of_eventuallyEq hn
  have hM := wirtingerBar_congr_of_eventuallyEq (hn.eventually_nhds.mono
    fun _ hw => wirtingerZ_congr_of_eventuallyEq hw)
  rw [hermitianQuadraticTensor_wirtingerZ hf hg A B C D hz,
    hermitianQuadraticTensor_wirtingerZ hf hg A' B' C' D' hz] at hZ
  rw [hermitianQuadraticTensor_wirtingerBar hf hg A B C D hz,
    hermitianQuadraticTensor_wirtingerBar hf hg A' B' C' D' hz] at hB
  rw [hermitianQuadraticTensor_mixed hU hf hg A B C D hz,
    hermitianQuadraticTensor_mixed hU hf hg A' B' C' D' hz] at hM
  have ⟨h₁, h₂, h₃, h₄⟩ := hermitianTensor_coefficients_eq_of_wirtinger_jet
    (f z) (g z) (deriv f z) (deriv g z)
    (A - A') (B - B') (C - C') (D - D') hW
    (by have h := hEq z hz; unfold hermitianQuadraticTensor at h; linear_combination h)
    (by unfold hermitianQuadraticTensorZ at hZ; linear_combination hZ)
    (by linear_combination hB) (by linear_combination hM)
  exact ⟨sub_eq_zero.mp h₁, sub_eq_zero.mp h₂, sub_eq_zero.mp h₃, sub_eq_zero.mp h₄⟩

end

end DOZZ.Proofs
