/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.BasisSpanning
public import DOZZ.Hypergeom.ClassificationWirtingerC2
import Mathlib.Analysis.Complex.RealDeriv

/-! The Cramer coefficients of a real Gauss PDE solution are antiholomorphic. -/

@[expose] public section

namespace DOZZ.Proofs

noncomputable def gaussCramerWronskian (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z * deriv g z - deriv f z * g z

noncomputable def gaussCramerNumerator₁ (T : ℂ → ℝ) (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  (T z : ℂ) * deriv g z -
    wirtingerZ (fun w => (T w : ℂ)) z * g z

noncomputable def gaussCramerNumerator₂ (T : ℂ → ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z * wirtingerZ (fun w => (T w : ℂ)) z - deriv f z * (T z : ℂ)

noncomputable def gaussCramerCoefficient₁ (T : ℂ → ℝ) (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  gaussCramerNumerator₁ T g z * (gaussCramerWronskian f g z)⁻¹

noncomputable def gaussCramerCoefficient₂ (T : ℂ → ℝ) (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  gaussCramerNumerator₂ T f z * (gaussCramerWronskian f g z)⁻¹

/-- On the regular slit plane, the two Cramer coefficients of a real PDE solution have zero
`∂z` derivative. The proof uses the scalar PDE as a first-order system for `(T, ∂z T)`;
the numerator and the Wronskian then satisfy the same Abel equation. -/
theorem realGaussCramerCoefficients_wirtingerZ_eq_zero
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
      DifferentiableAt ℝ (gaussCramerCoefficient₁ T f g) z ∧
        wirtingerZ (gaussCramerCoefficient₁ T f g) z = 0 ∧
      DifferentiableAt ℝ (gaussCramerCoefficient₂ T f g) z ∧
        wirtingerZ (gaussCramerCoefficient₂ T f g) z = 0 := by
  intro z hz
  have hzReg := gaussCutPlane_subset_regularPlane hz
  let D := z * (1 - z)
  have hD : D ≠ 0 := mul_ne_zero hzReg.1 (sub_ne_zero.mpr hzReg.2.symm)
  let p : ℂ := ((c : ℂ) - z * ((a : ℂ) + b + 1)) / D
  let q : ℂ := (a * b : ℂ) / D
  let t : ℂ → ℂ := fun w => T w
  let t₁ := wirtingerZ t
  have ht : ContDiffAt ℝ 2 t z := Complex.ofRealCLM.contDiff.contDiffAt.comp z
    ((hT.1 z hzReg).contDiffAt (gaussRegularPlane_isOpen.mem_nhds hzReg))
  have ht₂ : wirtingerZ t₁ z = -p * t₁ z + q * t z := by
    have h := hT.2 z hzReg
    change wirtingerZ t₁ z + p * t₁ z - q * t z = 0 at h
    linear_combination h
  have holomorphicData (u : ℂ → ℂ) (hu : AnalyticOnNhd ℂ u gaussCutPlane)
      (he : gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) u z = 0) :
      DifferentiableAt ℝ u z ∧ DifferentiableAt ℝ (deriv u) z ∧
        wirtingerZ u z = deriv u z ∧ wirtingerZ (deriv u) z = -p * deriv u z + q * u z := by
    have hu₀ := (hu z hz).differentiableAt
    have hu₁ := (hu.deriv z hz).differentiableAt
    refine ⟨hu₀.restrictScalars ℝ, hu₁.restrictScalars ℝ,
      wirtingerZ_eq_deriv_of_differentiableAt hu₀, ?_⟩
    rw [wirtingerZ_eq_deriv_of_differentiableAt hu₁]
    dsimp only [p, q]
    field_simp [hD]
    dsimp [D, gaussHolomorphicOperator] at he ⊢
    linear_combination he
  obtain ⟨hf₀, hf₁, hfz, hf₂⟩ := holomorphicData f hf (hODEf z hz)
  obtain ⟨hg₀, hg₁, hgz, hg₂⟩ := holomorphicData g hg (hODEg z hz)
  -- The determinant of any two solution columns obeys Abel's equation.
  have abel {u u₁ v v₁ : ℂ → ℂ}
      (hu : DifferentiableAt ℝ u z) (hu₁ : DifferentiableAt ℝ u₁ z)
      (hv : DifferentiableAt ℝ v z) (hv₁ : DifferentiableAt ℝ v₁ z)
      (hu' : wirtingerZ u z = u₁ z) (hv' : wirtingerZ v z = v₁ z)
      (hu₂ : wirtingerZ u₁ z = -p * u₁ z + q * u z)
      (hv₂ : wirtingerZ v₁ z = -p * v₁ z + q * v z) :
      let w := fun y => u y * v₁ y - u₁ y * v y
      DifferentiableAt ℝ w z ∧ wirtingerZ w z = -p * w z := by
    dsimp only
    have h₁ : DifferentiableAt ℝ (fun w => u w * v₁ w) z := hu.mul hv₁
    have h₂ : DifferentiableAt ℝ (fun w => u₁ w * v w) z := hu₁.mul hv
    refine ⟨h₁.sub h₂, ?_⟩
    rw [wirtingerZ_sub h₁ h₂, wirtingerZ_mul hu hv₁,
      wirtingerZ_mul hu₁ hv, hu', hv', hu₂, hv₂]
    ring
  let W := gaussCramerWronskian f g
  have hWAt : DifferentiableAt ℂ W z :=
    (((hf z hz).differentiableAt.mul (hg.deriv z hz).differentiableAt).sub
      ((hf.deriv z hz).differentiableAt.mul (hg z hz).differentiableAt))
  have hWz : deriv W z = -p * W z := (wirtingerZ_eq_deriv_of_differentiableAt hWAt).symm.trans
    (abel hf₀ hf₁ hg₀ hg₁ hfz hgz hf₂ hg₂).2
  have hWne := hW z hz
  have hInv : DifferentiableAt ℝ (fun w => (W w)⁻¹) z := (hWAt.inv hWne).restrictScalars ℝ
  have divide {A : ℂ → ℂ} (hA : DifferentiableAt ℝ A z ∧ wirtingerZ A z = -p * A z) :
      DifferentiableAt ℝ (fun w => A w * (W w)⁻¹) z ∧
        wirtingerZ (fun w => A w * (W w)⁻¹) z = 0 := by
    refine ⟨hA.1.mul hInv, ?_⟩
    rw [wirtingerZ_mul hA.1 hInv, hA.2, wirtingerZ_inv_of_differentiableAt hWAt hWne, hWz]
    field_simp [hWne]
    ring
  have ht₀ : DifferentiableAt ℝ t z := ht.differentiableAt (by norm_num)
  have ht₁ := differentiableAt_wirtingerZ_of_contDiffAt_two ht
  have hA := divide (abel ht₀ ht₁ hg₀ hg₁ rfl hgz ht₂ hg₂)
  have hB := divide (abel hf₀ hf₁ ht₀ ht₁ hfz rfl hf₂ ht₂)
  exact ⟨hA.1, hA.2, hB.1, hB.2⟩

end DOZZ.Proofs
