module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaLegendreModelCover
public import TaoTrudgianYang2025.BetaStationaryPoint

@[expose] public section

/-!
# Physical dual scales and the actual stationary exponent

Canonical charts use a multiplicative scale A. Their dual length is A*T/N
and their phase parameter is A^(1-1/sigma)*T. The identities below connect
these parameters to the original critical point, including the additive
phase factor and the Fourier conjugation convention.
-/

noncomputable section

open Expdb
open scoped FourierTransform

namespace TaoTrudgianYang2025


def modelPhaseDualScale (A T N : ℝ) : ℝ := A*T/N

def modelPhaseDualParameter (σ A T : ℝ) : ℝ := A^(1-σ⁻¹)*T

def modelPhaseDualOffset (F : ℝ → ℝ) (σ A w T : ℝ) : ℝ :=
  modelPhaseDualParameter σ A T * referenceModelPrimitive σ⁻¹ (w/A) -
    T * modelPhaseLegendreDual F w

theorem modelPhaseDualScale_pos {A T N : ℝ}
    (hA : 0 < A) (hT : 0 < T) (hN : 0 < N) :
    0 < modelPhaseDualScale A T N :=
  div_pos (mul_pos hA hT) hN

theorem modelPhaseDualScale_coordinate {A T N : ℝ}
    (hA : A ≠ 0) (hT : T ≠ 0) (hN : N ≠ 0) (r : ℝ) :
    r/modelPhaseDualScale A T N = (r*N/T)/A := by
  unfold modelPhaseDualScale
  field_simp

theorem modelPhaseDualParameter_cancel (σ : ℝ) {A : ℝ}
    (hA : 0 < A) (T : ℝ) :
    modelPhaseDualParameter σ A T * A^(σ⁻¹-1) = T := by
  have h : A^(1-σ⁻¹)*A^(σ⁻¹-1) = 1 := by
    rw [← Real.rpow_add hA,show 1-σ⁻¹+(σ⁻¹-1) = 0 by ring,Real.rpow_zero]
  unfold modelPhaseDualParameter
  calc
    A^(1-σ⁻¹)*T*A^(σ⁻¹-1) = (A^(1-σ⁻¹)*A^(σ⁻¹-1))*T := by ring
    _ = T := by rw [h,one_mul]


