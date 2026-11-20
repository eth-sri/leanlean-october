/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationHermitianDecomposition
public import DOZZ.Hypergeom.ClassificationWirtingerBarAnalytic

/-! The conjugate derivatives of a real solution are computed from its Cramer coefficients. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter
open scoped Topology

/-- Conjugating the real Gauss PDE gives its conjugate-Wirtinger form. -/
theorem realGaussSolution_conjugate_pde
    (a b c : ℝ) (T : ℂ → ℝ) (hT : IsRealGaussSolution a b c T)
    {z : ℂ} (hz : z ∈ gaussRegularPlane) :
    wirtingerBar (fun w => wirtingerBar (fun u => (T u : ℂ)) w) z +
        star (((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z))) *
          wirtingerBar (fun w => (T w : ℂ)) z -
        star ((a : ℂ) * b / (z * (1 - z))) * (T z : ℂ) = 0 := by
  let t := fun w => (T w : ℂ)
  have ht : (fun w => star (t w)) = t := by funext w; simp [t]
  have h := congrArg star (hT.2 z hz)
  rw [wirtingerBar_wirtingerBar_eq_star_wirtingerZ_wirtingerZ ht,
    show wirtingerBar t z = star (wirtingerZ t z) by unfold wirtingerBar; rw [ht]]
  simpa [t, ht] using h

private theorem wirtingerBar_basis_combination {f g A B T : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z)
    (hA : DifferentiableAt ℝ A z) (hB : DifferentiableAt ℝ B z)
    (he : T =ᶠ[𝓝 z] fun w => f w * A w + g w * B w) :
    wirtingerBar T z = f z * wirtingerBar A z + g z * wirtingerBar B z := by
  have hf' := hf.restrictScalars ℝ
  have hg' := hg.restrictScalars ℝ
  rw [wirtingerBar_congr_of_eventuallyEq he,
    wirtingerBar_add (f := fun w => f w * A w) (g := fun w => g w * B w) (hf'.mul hA) (hg'.mul hB),
    wirtingerBar_mul hf' hA, wirtingerBar_mul hg' hB,
    wirtingerBar_eq_zero_of_differentiableAt hf, wirtingerBar_eq_zero_of_differentiableAt hg]
  simp

/-- The first conjugate Wirtinger derivative of a real Gauss solution is the corresponding
combination of conjugate derivatives of its Cramer coefficients. -/
theorem realGaussCramer_wirtingerBar_expansion
    (a b c : ℝ) (T : ℂ → ℝ) (hT : IsRealGaussSolution a b c T)
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f gaussCutPlane)
    (hg : AnalyticOnNhd ℂ g gaussCutPlane)
    (hODEf : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) f z = 0)
    (hODEg : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) g z = 0)
    (hW : ∀ z ∈ gaussCutPlane, gaussCramerWronskian f g z ≠ 0) :
    ∀ z ∈ gaussCutPlane,
      wirtingerBar (fun w => (T w : ℂ)) z =
        f z * wirtingerBar (gaussCramerCoefficient₁ T f g) z +
          g z * wirtingerBar (gaussCramerCoefficient₂ T f g) z := by
  intro z hz
  obtain ⟨hA, _, hB, _⟩ := realGaussCramerCoefficients_wirtingerZ_eq_zero
    a b c T hT hf hg hODEf hODEg hW z hz
  apply wirtingerBar_basis_combination (hf z hz).differentiableAt (hg z hz).differentiableAt hA hB
  filter_upwards [gaussCutPlane_isOpen.mem_nhds hz] with w hw
  simpa only [mul_comm (f w), mul_comm (g w)] using (realGaussCramer_reconstruct T (hW w hw)).1

/-- The second conjugate Wirtinger derivative is likewise the basis-weighted sum of the second
conjugate derivatives of the coefficients. -/
theorem realGaussCramer_wirtingerBar_second_expansion
    (a b c : ℝ) (T : ℂ → ℝ) (hT : IsRealGaussSolution a b c T)
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f gaussCutPlane)
    (hg : AnalyticOnNhd ℂ g gaussCutPlane)
    (hODEf : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) f z = 0)
    (hODEg : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) g z = 0)
    (hW : ∀ z ∈ gaussCutPlane, gaussCramerWronskian f g z ≠ 0) :
    ∀ z ∈ gaussCutPlane,
      wirtingerBar (fun w => wirtingerBar (fun u => (T u : ℂ)) w) z =
        f z * wirtingerBar (fun w => wirtingerBar
          (gaussCramerCoefficient₁ T f g) w) z +
        g z * wirtingerBar (fun w => wirtingerBar
          (gaussCramerCoefficient₂ T f g) w) z := by
  intro z hz
  obtain ⟨hA, hB⟩ := realGaussCramer_conjugates_analytic a b c T hT hf hg hODEf hODEg hW
  apply wirtingerBar_basis_combination (hf z hz).differentiableAt (hg z hz).differentiableAt
    (differentiableAt_wirtingerBar_of_analytic_conjugate gaussCutPlane_isOpen hA hz)
    (differentiableAt_wirtingerBar_of_analytic_conjugate gaussCutPlane_isOpen hB hz)
  filter_upwards [gaussCutPlane_isOpen.mem_nhds hz] with w hw
  exact realGaussCramer_wirtingerBar_expansion a b c T hT hf hg hODEf hODEg hW w hw

/-- After expanding the conjugated real PDE in a holomorphic fundamental pair, the two Cramer
coefficients' conjugate Gauss residuals have zero basis-weighted sum. -/
theorem realGaussCramer_conjugate_pde_expansion
    (a b c : ℝ) (T : ℂ → ℝ) (hT : IsRealGaussSolution a b c T)
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f gaussCutPlane)
    (hg : AnalyticOnNhd ℂ g gaussCutPlane)
    (hODEf : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) f z = 0)
    (hODEg : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) g z = 0)
    (hW : ∀ z ∈ gaussCutPlane, gaussCramerWronskian f g z ≠ 0) :
    ∀ z ∈ gaussCutPlane,
      f z * (wirtingerBar (fun w => wirtingerBar
          (gaussCramerCoefficient₁ T f g) w) z +
          star (((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z))) *
            wirtingerBar (gaussCramerCoefficient₁ T f g) z -
          star ((a : ℂ) * b / (z * (1 - z))) *
            gaussCramerCoefficient₁ T f g z) +
        g z * (wirtingerBar (fun w => wirtingerBar
          (gaussCramerCoefficient₂ T f g) w) z +
          star (((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z))) *
            wirtingerBar (gaussCramerCoefficient₂ T f g) z -
          star ((a : ℂ) * b / (z * (1 - z))) *
            gaussCramerCoefficient₂ T f g z) = 0 := by
  intro z hz
  have hzReg := gaussCutPlane_subset_regularPlane hz
  have hPDE := realGaussSolution_conjugate_pde a b c T hT hzReg
  have hbar := realGaussCramer_wirtingerBar_expansion
    a b c T hT hf hg hODEf hODEg hW z hz
  have hbarbar := realGaussCramer_wirtingerBar_second_expansion
    a b c T hT hf hg hODEf hODEg hW z hz
  have hrec := (realGaussCramer_reconstruct T (hW z hz)).1
  rw [hbarbar, hbar, hrec] at hPDE
  linear_combination hPDE

end DOZZ.Proofs
