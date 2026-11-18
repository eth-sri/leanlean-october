/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationHermitianJets

/-! The mixed Wirtinger jet of a constant Hermitian tensor. -/

@[expose] public section

namespace DOZZ.Proofs

variable {f g : ℂ → ℂ} {U : Set ℂ}


open Filter
open scoped Topology


section
variable (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U) (k : ℂ) {z : ℂ} (hz : z ∈ U)
include hf hg k hz

private theorem wirtingerBar_deriv_term
 :
    wirtingerBar (fun w => k * deriv f w * star (g w)) z =
      k * deriv f z * star (deriv g z) := by
  have wirtingerBar_star_at (hg : DifferentiableAt ℂ g z) : wirtingerBar (fun w => star (g w)) z = star (deriv g z) := by
    unfold wirtingerBar
    have hfun : (fun w => star (star (g w))) = g := by
      funext w
      simp
    rw [hfun, wirtingerZ_eq_deriv_of_differentiableAt hg]
  have hf' := (hf.deriv z hz).differentiableAt
  have hgAt := (hg z hz).differentiableAt
  have hp : DifferentiableAt ℂ (fun w => k * deriv f w) z :=
    (differentiableAt_const k).mul hf'
  have hgStar : DifferentiableAt ℝ (fun w => star (g w)) z :=
    (Complex.differentiable_conj.differentiableAt (x := g z)).comp z
      (hgAt.restrictScalars ℝ)
  rw [wirtingerBar_mul (hp.restrictScalars ℝ) hgStar, wirtingerBar_eq_zero_of_differentiableAt hp,
    wirtingerBar_star_at hgAt]
  ring

private theorem hermitianTensorZ_termDiffAt
 :
    DifferentiableAt ℝ (fun w => k * deriv f w * star (g w)) z := by
  exact (((differentiableAt_const k).mul
      (hf.deriv z hz).differentiableAt).restrictScalars ℝ).mul
    ((Complex.differentiable_conj.differentiableAt (x := g z)).comp z
      ((hg z hz).differentiableAt.restrictScalars ℝ))


end
section
variable (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U) (A B C D : ℂ)
include hU hf hg A B C D

/-- The mixed conjugate Wirtinger derivative of a Hermitian tensor differentiates both
holomorphic factors. -/
theorem hermitianQuadraticTensor_mixed
 {z : ℂ} (hz : z ∈ U) :
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
  have hsum₁ : wirtingerBar (t₁ + t₂) z = wirtingerBar t₁ z + wirtingerBar t₂ z :=
    wirtingerBar_add (hermitianTensorZ_termDiffAt hf hf A hz)
      (hermitianTensorZ_termDiffAt hf hg B hz)
  have hsum₂ : wirtingerBar (t₃ + t₄) z = wirtingerBar t₃ z + wirtingerBar t₄ z :=
    wirtingerBar_add (hermitianTensorZ_termDiffAt hg hf C hz)
      (hermitianTensorZ_termDiffAt hg hg D hz)
  have hsum : wirtingerBar ((t₁ + t₂) + (t₃ + t₄)) z =
      wirtingerBar (t₁ + t₂) z + wirtingerBar (t₃ + t₄) z :=
    wirtingerBar_add
      ((hermitianTensorZ_termDiffAt hf hf A hz).add
        (hermitianTensorZ_termDiffAt hf hg B hz))
      ((hermitianTensorZ_termDiffAt hg hf C hz).add
        (hermitianTensorZ_termDiffAt hg hg D hz))
  have hfun : hermitianQuadraticTensorZ f g A B C D = (t₁ + t₂) + (t₃ + t₄) := by
    funext w
    simp [hermitianQuadraticTensorZ, t₁, t₂, t₃, t₄]
    ring
  have hcalc : wirtingerBar (hermitianQuadraticTensorZ f g A B C D) z =
      A * deriv f z * star (deriv f z) + B * deriv f z * star (deriv g z) +
        C * deriv g z * star (deriv f z) + D * deriv g z * star (deriv g z) := by
    calc
      _ = wirtingerBar ((t₁ + t₂) + (t₃ + t₄)) z := by rw [hfun]
      _ = wirtingerBar (t₁ + t₂) z + wirtingerBar (t₃ + t₄) z := hsum
      _ = wirtingerBar t₁ z + wirtingerBar t₂ z +
          (wirtingerBar t₃ z + wirtingerBar t₄ z) := by rw [hsum₁, hsum₂]
      _ = _ := by
        rw [show t₁ = fun w => A * deriv f w * star (f w) from rfl,
          show t₂ = fun w => B * deriv f w * star (g w) from rfl,
          show t₃ = fun w => C * deriv g w * star (f w) from rfl,
          show t₄ = fun w => D * deriv g w * star (g w) from rfl,
          (wirtingerBar_deriv_term hf hf A hz), wirtingerBar_deriv_term hf hg B hz, wirtingerBar_deriv_term hg hf C hz, wirtingerBar_deriv_term hg hg D hz]
        ring
  rw [wirtingerBar_congr_of_eventuallyEq hZdiff (hZdiff.congr_of_eventuallyEq hfirstNear.symm) hfirstNear, hcalc]

/-- Equality of Hermitian tensors on an open set determines all four coefficients whenever the
analytic basis has nonzero Wronskian. The value, both first Wirtinger derivatives, and the mixed
jet recover the coefficient matrix. -/
theorem hermitianTensor_coefficients_eq_of_eqOn
 (A' B' C' D' : ℂ) {z : ℂ} (hz : z ∈ U)
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
    exact hEq w hw
  have hQ₁diff := hQ₁At.differentiableAt (by norm_num)
  have hQ₂diff := hQ₂At.differentiableAt (by norm_num)
  have hZeq := wirtingerZ_congr_of_eventuallyEq hQ₁diff hQ₂diff hnear
  have hbareq := wirtingerBar_congr_of_eventuallyEq hQ₁diff hQ₂diff hnear
  have hZnear : (fun w => wirtingerZ Q₁ w) =ᶠ[𝓝 z]
      (fun w => wirtingerZ Q₂ w) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    have hnearW : Q₁ =ᶠ[𝓝 w] Q₂ := by
      filter_upwards [hU.mem_nhds hw] with v hv
      exact hEq v hv
    exact wirtingerZ_congr_of_eventuallyEq ((hermitianQuadraticTensor_contDiffAt_two hf hg A B C D hw).differentiableAt (by norm_num)) ((hermitianQuadraticTensor_contDiffAt_two hf hg A' B' C' D' hw).differentiableAt (by norm_num)) hnearW
  have h₀₀ :
      (A - A') * f z * star (f z) + (B - B') * f z * star (g z) +
        (C - C') * g z * star (f z) + (D - D') * g z * star (g z) = 0 := by
    calc
      _ = Q₁ z - Q₂ z := by dsimp [Q₁, Q₂, hermitianQuadraticTensor]; ring
      _ = 0 := sub_eq_zero.mpr (hEq z hz)
  have hZeq' :
      wirtingerZ (hermitianQuadraticTensor f g A B C D) z =
        wirtingerZ (hermitianQuadraticTensor f g A' B' C' D') z := by assumption
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
        wirtingerBar (hermitianQuadraticTensor f g A' B' C' D') z := by assumption
  have h₀₁raw := hbareq'
  rw [hermitianQuadraticTensor_wirtingerBar hf hg A B C D hz,
    hermitianQuadraticTensor_wirtingerBar hf hg A' B' C' D' hz] at h₀₁raw
  have h₀₁ :
      (A - A') * f z * star (deriv f z) + (B - B') * f z * star (deriv g z) +
        (C - C') * g z * star (deriv f z) + (D - D') * g z * star (deriv g z) = 0 := by
    calc
      _ = (A * f z * star (deriv f z) + B * f z * star (deriv g z) +
          C * g z * star (deriv f z) + D * g z * star (deriv g z)) -
        (A' * f z * star (deriv f z) + B' * f z * star (deriv g z) +
          C' * g z * star (deriv f z) + D' * g z * star (deriv g z)) := by ring
      _ = 0 := sub_eq_zero.mpr h₀₁raw
  have h₁₁raw := wirtingerBar_congr_of_eventuallyEq (differentiableAt_wirtingerZ_of_contDiffAt_two hQ₁At) (differentiableAt_wirtingerZ_of_contDiffAt_two hQ₂At) hZnear
  rw [hermitianQuadraticTensor_mixed hU hf hg A B C D hz,
    hermitianQuadraticTensor_mixed hU hf hg A' B' C' D' hz] at h₁₁raw
  have h₁₁ :
      (A - A') * deriv f z * star (deriv f z) +
        (B - B') * deriv f z * star (deriv g z) +
        (C - C') * deriv g z * star (deriv f z) +
        (D - D') * deriv g z * star (deriv g z) = 0 := by
    calc
      _ = (A * deriv f z * star (deriv f z) + B * deriv f z * star (deriv g z) +
          C * deriv g z * star (deriv f z) + D * deriv g z * star (deriv g z)) -
        (A' * deriv f z * star (deriv f z) + B' * deriv f z * star (deriv g z) +
          C' * deriv g z * star (deriv f z) + D' * deriv g z * star (deriv g z)) := by ring
      _ = 0 := sub_eq_zero.mpr h₁₁raw
  have hcoeff := hermitianTensor_coefficients_eq_of_wirtinger_jet
    (f z) (g z) (deriv f z) (deriv g z)
    (A - A') (B - B') (C - C') (D - D') hW h₀₀ h₁₀ h₀₁ h₁₁
  rcases hcoeff with ⟨hA, hB, hC, hD⟩
  exact ⟨sub_eq_zero.mp hA, sub_eq_zero.mp hB,
    sub_eq_zero.mp hC, sub_eq_zero.mp hD⟩


end
end DOZZ.Proofs
