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
noncomputable def gaussSystemCoeff₁ (a b z : ℂ) : ℂ :=
  (z * (1 - z))⁻¹ * (a * b)

/-- The second coefficient in the first-order Gauss system for the state `(f, f')`. -/
noncomputable def gaussSystemCoeff₂ (a b c z : ℂ) : ℂ :=
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

@[simp] theorem gaussSystemOperator_apply a b c z (y : ℂ × ℂ) :
    gaussSystemOperator a b c z y =
      (y.2, gaussSystemCoeff₁ a b z * y.1 + gaussSystemCoeff₂ a b c z * y.2) := by
  simp [gaussSystemOperator, gaussSystemCoeff₁, gaussSystemCoeff₂,
    ContinuousLinearMap.smulRight_apply]

theorem gaussRegularPlane_isOpen : IsOpen gaussRegularPlane := by
  change IsOpen ({z : ℂ | z ≠ 0} ∩ {z : ℂ | z ≠ 1})
  exact isOpen_ne.inter isOpen_ne



theorem gaussSystemOperator_differentiableOn a b c :
    DifferentiableOn ℂ (gaussSystemOperator a b c) gaussRegularPlane := by
  have gaussSystemCoeff₂_differentiableOn : DifferentiableOn ℂ (gaussSystemCoeff₂ a b c) gaussRegularPlane := by
    have hden_ne : ∀ z ∈ gaussRegularPlane, z * (1 - z) ≠ 0 := by
      intro z hz
      apply mul_ne_zero hz.1
      intro hz'
      apply hz.2
      linear_combination -hz'
    change DifferentiableOn ℂ
      (fun z : ℂ => (z * (1 - z))⁻¹ * ((a + b + 1) * z - c)) gaussRegularPlane
    exact ((differentiableOn_id.mul ((differentiableOn_const 1).sub differentiableOn_id) : DifferentiableOn ℂ (fun z => z * (1 - z)) gaussRegularPlane).inv hden_ne).mul ((differentiableOn_const (a + b + 1)).mul differentiableOn_id |>.sub (differentiableOn_const c))
  have gaussSystemCoeff₁_differentiableOn : DifferentiableOn ℂ (gaussSystemCoeff₁ a b) gaussRegularPlane := by
    have hden_ne : ∀ z ∈ gaussRegularPlane, z * (1 - z) ≠ 0 := by
      intro z hz
      apply mul_ne_zero hz.1
      intro hz'
      apply hz.2
      linear_combination -hz'
    change DifferentiableOn ℂ (fun z : ℂ => (z * (1 - z))⁻¹ * (a * b)) gaussRegularPlane
    exact ((differentiableOn_id.mul ((differentiableOn_const 1).sub differentiableOn_id) : DifferentiableOn ℂ (fun z => z * (1 - z)) gaussRegularPlane).inv hden_ne).mul_const (a * b)
  let secondOutput : ℂ →L[ℂ] ℂ × ℂ :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (0, 1)
  let firstComponent : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
    ((ContinuousLinearMap.id ℂ ℂ).smulRight (1, 0)).comp (ContinuousLinearMap.snd ℂ ℂ ℂ)
  let secondFromFirst := secondOutput.comp (ContinuousLinearMap.fst ℂ ℂ ℂ)
  let secondFromSecond := secondOutput.comp (ContinuousLinearMap.snd ℂ ℂ ℂ)
  change DifferentiableOn ℂ
    (fun z => firstComponent + (gaussSystemCoeff₁ a b z • secondFromFirst +
      gaussSystemCoeff₂ a b c z • secondFromSecond)) gaussRegularPlane
  exact (differentiableOn_const _ : DifferentiableOn ℂ (fun _ : ℂ => firstComponent) gaussRegularPlane).add ((gaussSystemCoeff₁_differentiableOn |>.smul (differentiableOn_const _ : DifferentiableOn ℂ (fun _ : ℂ => secondFromFirst) gaussRegularPlane)).add (gaussSystemCoeff₂_differentiableOn |>.smul (differentiableOn_const _ : DifferentiableOn ℂ (fun _ : ℂ => secondFromSecond) gaussRegularPlane)))


theorem gaussHolomorphicOperator_eq_zero_iff_system_residual_eq_zero
    a b c (f : ℂ → ℂ) {z}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    gaussHolomorphicOperator a b c f z = 0 ↔
      deriv (deriv f) z =
        gaussSystemCoeff₁ a b z * f z + gaussSystemCoeff₂ a b c z * deriv f z := by
  have gaussHolomorphicOperator_eq_mul_system_residual : gaussHolomorphicOperator a b c f z = z * (1 - z) * (deriv (deriv f) z - (gaussSystemCoeff₁ a b z * f z + gaussSystemCoeff₂ a b c z * deriv f z)) := by
    simp only [gaussHolomorphicOperator, gaussSystemCoeff₁, gaussSystemCoeff₂]
    field_simp
    ring
  rw [gaussHolomorphicOperator_eq_mul_system_residual]
  constructor
  · intro h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (mul_ne_zero hz0 (sub_ne_zero.mpr (Ne.symm hz1))))
  · intro h
    simp [h]

end DOZZ.Proofs
