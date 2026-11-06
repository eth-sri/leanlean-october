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
variable {f g : ℂ → ℂ} {U : Set ℂ}
section
variable (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U) (k : ℂ) {z : ℂ} (hz : z ∈ U)
include hf hg hz

private theorem wirtingerBar_deriv_term
    :
    wirtingerBar (fun w => k * deriv f w * star (g w)) z =
      k * deriv f z * star (deriv g z) := by
  have hgAt := (hg z hz).differentiableAt
  have hp : DifferentiableAt ℂ (fun w => k * deriv f w) z :=
    (differentiableAt_const k).mul ((hf.deriv z hz).differentiableAt)
  have hgStar : DifferentiableAt ℝ (fun w => star (g w)) z :=
    (Complex.differentiable_conj.differentiableAt).comp z
      (hgAt.restrictScalars ℝ)
  rw [(wirtingerBar_mul (hp.restrictScalars ℝ) hgStar), wirtingerBar_eq_zero_of_differentiableAt hp,
    DOZZ.Proofs.wirtingerBar_star_eq_star_deriv_at hgAt]
  ring

private theorem hermitianTensorZ_termDiffAt
    :
    DifferentiableAt ℝ (fun w => k * deriv f w * star (g w)) z := (((differentiableAt_const k).mul
      (hf.deriv z hz).differentiableAt).restrictScalars ℝ).mul
    ((Complex.differentiable_conj.differentiableAt).comp z
      ((hg z hz).differentiableAt.restrictScalars ℝ))

end
section
variable (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
include hU hf hg

/-- The mixed conjugate Wirtinger derivative of a Hermitian tensor differentiates both
holomorphic factors. -/
theorem hermitianQuadraticTensor_mixed
    (A B C D : ℂ) {z : ℂ} (hz : z ∈ U) :
    wirtingerBar (fun w => wirtingerZ (hermitianQuadraticTensor f g A B C D) w) z =
      A * deriv f z * star (deriv f z) + B * deriv f z * star (deriv g z) +
        C * deriv g z * star (deriv f z) + D * deriv g z * star (deriv g z) := by
  let t₁ : ℂ → ℂ := fun w => A * deriv f w * star (f w)
  let t₂ : ℂ → ℂ := fun w => B * deriv f w * star (g w)
  let t₃ : ℂ → ℂ := fun w => C * deriv g w * star (f w)
  let t₄ : ℂ → ℂ := fun w => D * deriv g w * star (g w)
  have hZdiff := differentiableAt_wirtingerZ_of_contDiffAt_two (hermitianQuadraticTensor_contDiffAt_two hf hg A B C D hz)
  have hfirstNear : (fun w => wirtingerZ (hermitianQuadraticTensor f g A B C D) w) =ᶠ[𝓝 z]
      hermitianQuadraticTensorZ f g A B C D := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hermitianQuadraticTensor_wirtingerZ hf hg A B C D hw
  have hZtensorDiff :=
    hZdiff.congr_of_eventuallyEq hfirstNear.symm
  have hbar := wirtingerBar_congr_of_eventuallyEq hZdiff hZtensorDiff hfirstNear
  have hterm₁ := wirtingerBar_deriv_term hf hf A hz
  have hterm₂ := wirtingerBar_deriv_term hf hg B hz
  have hterm₃ := wirtingerBar_deriv_term hg hf C hz
  have hterm₄ := wirtingerBar_deriv_term hg hg D hz
  have hsum₁ : wirtingerBar (t₁ + t₂) z = wirtingerBar t₁ z + wirtingerBar t₂ z :=
    wirtingerBar_add (hermitianTensorZ_termDiffAt hf hf A hz)
      (hermitianTensorZ_termDiffAt hf hg B hz)
  have hsum₂ : wirtingerBar (t₃ + t₄) z = wirtingerBar t₃ z + wirtingerBar t₄ z :=
    wirtingerBar_add (hermitianTensorZ_termDiffAt hg hf C hz)
      (hermitianTensorZ_termDiffAt hg hg D hz)
  have hsum : wirtingerBar ((t₁ + t₂) + (t₃ + t₄)) z =
      wirtingerBar _ z + wirtingerBar _ z :=
    wirtingerBar_add
      ((hermitianTensorZ_termDiffAt hf hf A hz).add
        (hermitianTensorZ_termDiffAt hf hg B hz))
      ((hermitianTensorZ_termDiffAt hg hf C hz).add
        (hermitianTensorZ_termDiffAt hg hg D hz))
  have hfun : hermitianQuadraticTensorZ f g A B C D = (t₁ + t₂) + (t₃ + t₄) := by
    funext w
    simp [hermitianQuadraticTensorZ, t₁, t₂, t₃, t₄]
    ring
  grind

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
  let Q₁ := hermitianQuadraticTensor f g A B C D
  let Q₂ := hermitianQuadraticTensor f g A' B' C' D'
  have hQ₁At := hermitianQuadraticTensor_contDiffAt_two hf hg A B C D hz
  have hQ₂At := hermitianQuadraticTensor_contDiffAt_two hf hg A' B' C' D' hz
  have hnear : Q₁ =ᶠ[𝓝 z] Q₂ := by
    filter_upwards [hU.mem_nhds hz] with w hw
    tauto
  have hQ₁diff := hQ₁At.differentiableAt (by norm_num)
  have hQ₂diff := hQ₂At.differentiableAt (by norm_num)
  have hbareq := wirtingerBar_congr_of_eventuallyEq hQ₁diff hQ₂diff hnear
  have hZ₁diff := differentiableAt_wirtingerZ_of_contDiffAt_two hQ₁At
  have hZ₂diff := differentiableAt_wirtingerZ_of_contDiffAt_two hQ₂At
  have hZnear : (wirtingerZ Q₁) =ᶠ[𝓝 z]
      (wirtingerZ Q₂) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    have hQ₁AtW := hermitianQuadraticTensor_contDiffAt_two hf hg A B C D hw
    have hQ₂AtW := hermitianQuadraticTensor_contDiffAt_two hf hg A' B' C' D' hw
    have hQ₁diffW := hQ₁AtW.differentiableAt (by norm_num)
    have hQ₂diffW := hQ₂AtW.differentiableAt (by norm_num)
    have hnearW : Q₁ =ᶠ[𝓝 w] Q₂ := by
      filter_upwards [hU.mem_nhds hw] with v hv
      exact hEq v hv
    exact wirtingerZ_congr_of_eventuallyEq hQ₁diffW hQ₂diffW hnearW
  have hmixeq := wirtingerBar_congr_of_eventuallyEq hZ₁diff hZ₂diff hZnear
  have h₀₀ :
      (A - A') * f z * star (f z) + (B - B') * f z * star (g z) +
        (C - C') * g z * star (f z) + (D - D') * g z * star (g z) = 0 := by
    calc
      _ = Q₁ z - Q₂ z := by dsimp [Q₁, Q₂, hermitianQuadraticTensor]; ring
      _ = 0 := by aesop
  have hZeq' :
      wirtingerZ (hermitianQuadraticTensor f g A B C D) z =
        wirtingerZ (hermitianQuadraticTensor f g A' B' C' D') z := by
    simpa [Q₁, Q₂] using (wirtingerZ_congr_of_eventuallyEq hQ₁diff hQ₂diff hnear)
  have h₁₀raw := hZeq'
  rw [hermitianQuadraticTensor_wirtingerZ hf hg A B C D hz,
    hermitianQuadraticTensor_wirtingerZ hf hg A' B' C' D' hz] at h₁₀raw
  have h₁₀ :
      (A - A') * deriv f z * star (f z) + (B - B') * deriv f z * star (g z) +
        (C - C') * deriv g z * star (f z) + (D - D') * deriv g z * star (g z) = 0 := by
    calc
      _ = hermitianQuadraticTensorZ f g A B C D z -
          hermitianQuadraticTensorZ f g A' B' C' D' z := by
        simp [hermitianQuadraticTensorZ]
        ring
      _ = 0 := sub_eq_zero.mpr h₁₀raw
  have hbareq' :
      wirtingerBar (hermitianQuadraticTensor f g A B C D) z =
        wirtingerBar (hermitianQuadraticTensor f g A' B' C' D') z := by
    simpa [Q₁, Q₂] using hbareq
  have h₀₁raw := hbareq'
  rw [hermitianQuadraticTensor_wirtingerBar hf hg A B C D hz,
    hermitianQuadraticTensor_wirtingerBar hf hg A' B' C' D' hz] at h₀₁raw
  have h₀₁ :
      (A - A') * f z * star (deriv f z) + (B - B') * f z * star (deriv g z) +
        (C - C') * g z * star (deriv f z) + (D - D') * g z * star (deriv g z) = 0 := by
    calc
      _ = (A * f z * star _ + B * f z * star _ +
          C * g z * star _ + D * g z * star _) -
        (A' * f z * star _ + B' * f z * star _ +
          C' * g z * star _ + D' * g z * star _) := by ring
      _ = 0 := sub_eq_zero.mpr h₀₁raw
  have h₁₁raw := hmixeq
  rw [hermitianQuadraticTensor_mixed hU hf hg A B C D hz,
    hermitianQuadraticTensor_mixed hU hf hg A' B' C' D' hz] at h₁₁raw
  have h₁₁ :
      (A - A') * deriv f z * star (deriv f z) +
        (B - B') * deriv f z * star (deriv g z) +
        (C - C') * deriv g z * star (deriv f z) +
        (D - D') * deriv g z * star (deriv g z) = 0 := by
    calc
      _ = (A * deriv f z * star _ + B * deriv f z * star _ +
          C * deriv g z * star _ + D * deriv g z * star _) -
        (A' * deriv f z * star _ + B' * deriv f z * star _ +
          C' * deriv g z * star _ + D' * deriv g z * star _) := by ring
      _ = 0 := sub_eq_zero.mpr h₁₁raw
  have hcoeff := hermitianTensor_coefficients_eq_of_wirtinger_jet
    (f z) (g z) _ _
    (A - A') _ _ _ hW h₀₀ h₁₀ h₀₁ h₁₁
  rcases hcoeff with ⟨hA, hB, hC, hD⟩
  exact ⟨sub_eq_zero.mp hA, sub_eq_zero.mp hB,
    sub_eq_zero.mp hC, sub_eq_zero.mp hD⟩

end

end

end DOZZ.Proofs
