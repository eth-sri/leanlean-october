/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.KernelIntegrability
import BergmanWeakType.Weighted.CompactIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Tactic
import BergmanWeakType.RpowRing

/-! # Pure radial and angular derivatives of the weighted kernel -/



noncomputable section

open Real


namespace BergmanWeakType.Weighted

def polarOperator (k r u ur urr utt : ℝ) : ℝ :=
  urr + (1 / r - 2 * k * r / (1 - r ^ 2)) * ur + utt / r ^ 2 - k ^ 2 / (1 - r ^ 2) * u

variable (q k α : ℝ) (w : ℂ) (r θ : ℝ)

def radialComponent : ℝ := w.re * cos θ + w.im * sin θ
def angularComponent : ℝ := w.im * cos θ - w.re * sin θ

local notation "ρ" => radialComponent w θ
local notation "τ" => angularComponent w θ
local notation "σ" => ‖w‖ ^ 2

theorem component_norm_sq :
    ρ ^ 2 + τ ^ 2 = σ := by
  simp only [Complex.sq_norm, Complex.normSq_apply]
  grind [Real.sin_sq_add_cos_sq, mul_one, radialComponent, angularComponent]

def polarDenominator : ℝ :=
  σ * r ^ 2 - 2 * r * ρ + 1

local notation "D" => polarDenominator w r θ

def polarKernel : ℝ := D ^ q

local notation "K₁" => polarKernel (q - 1) w r θ
local notation "K₂" => polarKernel (q - 2) w r θ

def polarKernelR : ℝ :=
  2 * q * (σ * r - ρ) * K₁

def polarKernelRR : ℝ :=
  2 * q * σ * K₁ +
    4 * q * (q - 1) * (σ * r - ρ) ^ 2 *
      K₂

def polarKernelT : ℝ :=
  -2 * q * r * τ * K₁

def polarKernelTT : ℝ :=
  2 * q * r * ρ * K₁ +
    4 * q * (q - 1) * r ^ 2 * τ ^ 2 * K₂

theorem polarDenominator_pos {w : ℂ} {r} (hr : r ^ 2 < 1)
    (hw : ‖w‖ ^ 2 ≤ 1) (θ ) : 0 < polarDenominator w r θ := by
  have hc := component_norm_sq w θ
  unfold polarDenominator
  nlinarith [sq_nonneg (r * angularComponent w θ),
    sq_pos_of_pos (show 0 < 1 - r * radialComponent w θ by nlinarith)]

theorem polarKernel_laplacian
    (hd : 0 < D) (hr : r ≠ 0) :
    polarKernelRR q w r θ + polarKernelR q w r θ / r +
      polarKernelTT q w r θ / r ^ 2 =
        4 * q ^ 2 * σ * K₁ := by
  have hc := component_norm_sq w θ
  dsimp [polarKernelRR, polarKernelR, polarKernelTT, polarKernel]
  simp only [Real.rpow_sub hd, Real.rpow_one, Real.rpow_two]
  field_simp [hr, hd.ne']
  grind [polarDenominator]

/-- The weighted elliptic equation in polar coordinates, with no mixed derivatives. -/
theorem polarKernel_equation
    (hd : 0 < D) (hr : r ≠ 0) (ht : 1 - r ^ 2 ≠ 0) :
    let q := -k / 2
    polarOperator k r (polarKernel q w r θ) (polarKernelR q w r θ)
      (polarKernelRR q w r θ) (polarKernelTT q w r θ) =
        -(k ^ 2 * (1 - σ)) /
          ((1 - r ^ 2) * D) * polarKernel q w r θ := by
  dsimp [polarOperator]
  rw [sub_mul, one_div_mul_eq_div, ← add_sub_assoc, sub_add_eq_add_sub,
    polarKernel_laplacian _ w r θ hd hr]
  unfold polarKernelR polarKernel
  rw [Real.rpow_sub_one hd.ne']
  field_simp [hr, ht, hd.ne']
  unfold polarDenominator
  ring

theorem polarDenominator_eq_norm_sq : polarDenominator w r θ = ‖1 - circleMap 0 r θ * star w‖ ^ 2 :=
  by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, circleMap_zero_re, circleMap_zero_im,
    polarDenominator, radialComponent, Complex.sq_norm]
  grind [Real.cos_sq_add_sin_sq]

theorem polarKernel_eq_norm_weightedKernel :
    polarKernel (-(α + 2) / 2) w r θ = ‖weightedKernel α (circleMap 0 r θ) w‖ := by
  rw [polarKernel, polarDenominator_eq_norm_sq, norm_weightedKernel,
    ← Real.rpow_natCast_mul (norm_nonneg _) 2]
  ring

end BergmanWeakType.Weighted
