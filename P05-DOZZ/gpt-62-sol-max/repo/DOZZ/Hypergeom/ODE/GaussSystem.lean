/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! The Gauss scalar equation as a first-order holomorphic system on its regular domain. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

/-- The first coefficient in the first-order Gauss system for the state `(f, f')`. -/
noncomputable def gaussSystemCoeff₁ (a b : ℂ) (z : ℂ) : ℂ :=
  (z * (1 - z))⁻¹ * (a * b)

/-- The second coefficient in the first-order Gauss system for the state `(f, f')`. -/
noncomputable def gaussSystemCoeff₂ (a b c : ℂ) (z : ℂ) : ℂ :=
  (z * (1 - z))⁻¹ * ((a + b + 1) * z - c)

/-- Coefficient operator for the Gauss first-order system on `ℂ × ℂ`. -/
noncomputable def gaussSystemOperator (a b c z : ℂ) :
    ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  let firstOutput : ℂ →L[ℂ] ℂ × ℂ :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (1, 0)
  let secondOutput : ℂ →L[ℂ] ℂ × ℂ :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (0, 1)
  (firstOutput.comp (ContinuousLinearMap.snd ℂ ℂ ℂ)) +
    ((gaussSystemCoeff₁ a b z) • (secondOutput.comp (ContinuousLinearMap.fst ℂ ℂ ℂ)) +
      (gaussSystemCoeff₂ a b c z) • (secondOutput.comp (ContinuousLinearMap.snd ℂ ℂ ℂ)))

@[simp] theorem gaussSystemOperator_apply (a b c z : ℂ) (y : ℂ × ℂ) :
    gaussSystemOperator a b c z y =
      (y.2, gaussSystemCoeff₁ a b z * y.1 + gaussSystemCoeff₂ a b c z * y.2) := by
  simp [gaussSystemOperator, gaussSystemCoeff₁, gaussSystemCoeff₂,
    ContinuousLinearMap.smulRight_apply]

theorem gaussRegularPlane_isOpen : IsOpen gaussRegularPlane := by
  change IsOpen ({z : ℂ | z ≠ 0} ∩ {z : ℂ | z ≠ 1})
  exact isOpen_ne.inter isOpen_ne

private theorem gaussSystem_inv_differentiableOn :
    DifferentiableOn ℂ (fun z : ℂ => (z * (1 - z))⁻¹) gaussRegularPlane :=
  (differentiableOn_id.mul ((differentiableOn_const 1).sub differentiableOn_id)).inv
    (fun _ hz => mul_ne_zero hz.1 (sub_ne_zero.mpr (Ne.symm hz.2)))

theorem gaussSystemCoeff₁_differentiableOn (a b : ℂ) :
    DifferentiableOn ℂ (gaussSystemCoeff₁ a b) gaussRegularPlane :=
  gaussSystem_inv_differentiableOn.mul_const _

theorem gaussSystemCoeff₂_differentiableOn (a b c : ℂ) :
    DifferentiableOn ℂ (gaussSystemCoeff₂ a b c) gaussRegularPlane :=
  gaussSystem_inv_differentiableOn.mul
    (((differentiableOn_const (a + b + 1)).mul differentiableOn_id).sub_const c)

theorem gaussSystemOperator_differentiableOn (a b c : ℂ) :
    DifferentiableOn ℂ (gaussSystemOperator a b c) gaussRegularPlane := by
  unfold gaussSystemOperator
  exact (differentiableOn_const _).add
    (((gaussSystemCoeff₁_differentiableOn a b).smul (differentiableOn_const _)).add
      ((gaussSystemCoeff₂_differentiableOn a b c).smul (differentiableOn_const _)))

section
variable (a b c : ℂ) (f : ℂ → ℂ) {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1)
include hz0 hz1

theorem gaussHolomorphicOperator_eq_mul_system_residual :
    gaussHolomorphicOperator a b c f z =
      z * (1 - z) * (deriv (deriv f) z -
        (gaussSystemCoeff₁ a b z * f z + gaussSystemCoeff₂ a b c z * deriv f z)) := by
  have hden : z * (1 - z) ≠ 0 := mul_ne_zero hz0 (sub_ne_zero.mpr (Ne.symm hz1))
  simp only [gaussHolomorphicOperator, gaussSystemCoeff₁, gaussSystemCoeff₂]
  field_simp
  ring

theorem gaussHolomorphicOperator_eq_zero_iff_system_residual_eq_zero :
    gaussHolomorphicOperator a b c f z = 0 ↔
      deriv (deriv f) z =
        gaussSystemCoeff₁ a b z * f z + gaussSystemCoeff₂ a b c z * deriv f z := by
  rw [gaussHolomorphicOperator_eq_mul_system_residual a b c f hz0 hz1]
  have hden : z * (1 - z) ≠ 0 := mul_ne_zero hz0 (sub_ne_zero.mpr (Ne.symm hz1))
  constructor
  · intro h
    have hres := (mul_eq_zero.mp h).resolve_left hden
    exact sub_eq_zero.mp hres
  · intro h
    simp [h]

end

end DOZZ.Proofs
