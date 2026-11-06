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
  have realGaussCramer_wirtingerBar_expansion : ∀ z ∈ gaussCutPlane, wirtingerBar (fun w => (T w : ℂ)) z = f z * wirtingerBar (gaussCramerCoefficient₁ T f g) z + g z * wirtingerBar (gaussCramerCoefficient₂ T f g) z := by
    intro z hz
    have hzReg := gaussCutPlane_subset_regularPlane hz
    have ht0 : DifferentiableAt ℝ (fun w => (T w : ℂ)) z :=
      (show ContDiffAt ℝ 2 (fun w => (T w : ℂ)) z by change ContDiffAt ℝ 2 (fun w => Complex.ofRealCLM (T w)) z; exact Complex.ofRealCLM.contDiff.contDiffAt.comp z ((hT.1 z hzReg).contDiffAt (gaussRegularPlane_isOpen.mem_nhds hzReg))).differentiableAt (by norm_num)
    obtain ⟨hαAt, _, hβAt, _⟩ := (realGaussCramerCoefficients_wirtingerZ_eq_zero a b c T hT hf hg hODEf hODEg hW) z hz
    have hfAt := (hf z hz).differentiableAt
    have hgAt := (hg z hz).differentiableAt
    calc
      wirtingerBar (fun w => (T w : ℂ)) z =
          wirtingerBar (fun w => gaussCramerCoefficient₁ T f g w * f w +
            gaussCramerCoefficient₂ T f g w * g w) z :=
        wirtingerBar_congr_of_eventuallyEq ht0 ((hαAt.mul (hfAt.restrictScalars ℝ)).add (hβAt.mul (hgAt.restrictScalars ℝ))) (by filter_upwards [gaussCutPlane_isOpen.mem_nhds hz] with w hw; exact (realGaussCramer_reconstruct T (hW w hw)).1)
      _ = f z * wirtingerBar (gaussCramerCoefficient₁ T f g) z +
            g z * wirtingerBar (gaussCramerCoefficient₂ T f g) z := by
        have h₁At : DifferentiableAt ℝ
            (fun w => gaussCramerCoefficient₁ T f g w * f w) z :=
          hαAt.mul (hfAt.restrictScalars ℝ)
        have h₂At : DifferentiableAt ℝ
            (fun w => gaussCramerCoefficient₂ T f g w * g w) z :=
          hβAt.mul (hgAt.restrictScalars ℝ)
        rw [wirtingerBar_add h₁At h₂At,
          wirtingerBar_mul hαAt (hfAt.restrictScalars ℝ),
          wirtingerBar_mul hβAt (hgAt.restrictScalars ℝ),
          wirtingerBar_eq_zero_of_differentiableAt hfAt,
          wirtingerBar_eq_zero_of_differentiableAt hgAt]
        ring
  have realGaussCramer_wirtingerBar_second_expansion : ∀ z ∈ gaussCutPlane, wirtingerBar (fun w => wirtingerBar (fun u => (T u : ℂ)) w) z = f z * wirtingerBar (fun w => wirtingerBar (gaussCramerCoefficient₁ T f g) w) z + g z * wirtingerBar (fun w => wirtingerBar (gaussCramerCoefficient₂ T f g) w) z := by
    intro z hz
    have hzReg := gaussCutPlane_subset_regularPlane hz
    let t0 : ℂ → ℂ := fun w => (T w : ℂ)
    have hbarTfun : (fun w => wirtingerBar t0 w) =
        (fun w => star (wirtingerZ t0 w)) := by
      funext w
      unfold wirtingerBar
      rw [(show (fun w => star (t0 w)) = t0 by funext w; simp [t0])]
    have hconjAnalytic := realGaussCramer_conjugates_analytic
      a b c T hT hf hg hODEf hODEg hW
    obtain ⟨hαAt, _, hβAt, _⟩ := (realGaussCramerCoefficients_wirtingerZ_eq_zero a b c T hT hf hg hODEf hODEg hW) z hz
    have hαBarAt := differentiableAt_wirtingerBar_of_analytic_conjugate
      gaussCutPlane_isOpen hconjAnalytic.1 hz
    have hβBarAt := differentiableAt_wirtingerBar_of_analytic_conjugate
      gaussCutPlane_isOpen hconjAnalytic.2 hz
    have hfAt := (hf z hz).differentiableAt
    have hgAt := (hg z hz).differentiableAt
    let S : ℂ → ℂ := fun w =>
      f w * wirtingerBar (gaussCramerCoefficient₁ T f g) w +
        g w * wirtingerBar (gaussCramerCoefficient₂ T f g) w
    have hS₁At := (hfAt.restrictScalars ℝ).mul hαBarAt
    have hS₂At := (hgAt.restrictScalars ℝ).mul hβBarAt
    have hSbar : wirtingerBar S z =
        f z * wirtingerBar (fun w => wirtingerBar
            (gaussCramerCoefficient₁ T f g) w) z +
          g z * wirtingerBar (fun w => wirtingerBar
            (gaussCramerCoefficient₂ T f g) w) z := by
      calc
        wirtingerBar S z =
            wirtingerBar (fun w => f w * wirtingerBar
              (gaussCramerCoefficient₁ T f g) w) z +
            wirtingerBar (fun w => g w * wirtingerBar
              (gaussCramerCoefficient₂ T f g) w) z := by
          exact wirtingerBar_add hS₁At hS₂At
        _ = _ := by
          rw [wirtingerBar_mul (hfAt.restrictScalars ℝ) hαBarAt,
            wirtingerBar_mul (hgAt.restrictScalars ℝ) hβBarAt,
            wirtingerBar_eq_zero_of_differentiableAt hfAt,
            wirtingerBar_eq_zero_of_differentiableAt hgAt]
          ring
    calc
      wirtingerBar (fun w => wirtingerBar t0 w) z = wirtingerBar S z :=
        wirtingerBar_congr_of_eventuallyEq (by rw [hbarTfun]; exact (Complex.differentiable_conj.differentiableAt (x := wirtingerZ t0 z)).comp z (differentiableAt_wirtingerZ_of_contDiffAt_two (by change ContDiffAt ℝ 2 (fun w => Complex.ofRealCLM (T w)) z; exact Complex.ofRealCLM.contDiff.contDiffAt.comp z ((hT.1 z hzReg).contDiffAt (gaussRegularPlane_isOpen.mem_nhds hzReg))))) (by dsimp [S]; exact hS₁At.add hS₂At) (show (fun w => wirtingerBar t0 w) =ᶠ[𝓝 z] S by filter_upwards [gaussCutPlane_isOpen.mem_nhds hz] with w hw; exact realGaussCramer_wirtingerBar_expansion w hw)
      _ = _ := hSbar
  have realGaussSolution_conjugate_pde {z : ℂ} (hz : z ∈ gaussRegularPlane) : wirtingerBar (fun w => wirtingerBar (fun u => (T u : ℂ)) w) z + star (((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z))) * wirtingerBar (fun w => (T w : ℂ)) z - star ((a : ℂ) * b / (z * (1 - z))) * (T z : ℂ) = 0 := by
    let t : ℂ → ℂ := fun w => (T w : ℂ)
    have hself : (fun w => star (t w)) = t := by
      funext w
      simp [t]
    rw [wirtingerBar_wirtingerBar_eq_star_wirtingerZ_wirtingerZ hself]
    rw [(show wirtingerBar t z = star (wirtingerZ t z) by unfold wirtingerBar; rw [hself])]
    exact (by simpa [t, hself] using (congrArg star (hT.2 z hz)))
  intro z hz
  have hPDE := realGaussSolution_conjugate_pde (gaussCutPlane_subset_regularPlane hz)
  rw [(realGaussCramer_wirtingerBar_second_expansion z hz), (realGaussCramer_wirtingerBar_expansion z hz), ((realGaussCramer_reconstruct T (hW z hz)).1)] at hPDE
  linear_combination hPDE

end DOZZ.Proofs
