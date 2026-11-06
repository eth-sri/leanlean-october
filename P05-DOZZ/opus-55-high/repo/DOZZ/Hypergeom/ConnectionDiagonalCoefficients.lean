/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussCoefficientRatio
public import DOZZ.Hypergeom.ODE.ConnectionGammaCoefficients

/-! Gamma algebra for the real diagonal connection constraint. -/

@[expose] public section

namespace DOZZ.Proofs

/-- On the nondegenerate `K₂` locus, the coefficient ratio of [KRV, (Fundrelation)] solves the
undivided diagonal constraint. The proof retains the cases where a denominator Gamma is a pole: then
both the corresponding `K₁` factor and the totalized quotient vanish. -/
theorem gaussCoefficientRatio_mul_K₂_add_K₁_eq_zero
    (a b c : ℝ) (hK₂ : gaussK₂ a b c ≠ 0) :
    gaussCoefficientRatio a b c * gaussK₂ a b c + gaussK₁ a b c = 0 := by
  let d := Real.Gamma (c - a) * Real.Gamma (c - b) *
    Real.Gamma a * Real.Gamma b
  have hGamma₂c : Real.Gamma (2 - c) ≠ 0 := by
    intro h
    apply hK₂
    simp [gaussK₂, h]
  have hInv₁a : (Real.Gamma (1 - a))⁻¹ ≠ 0 := by
    intro h
    apply hK₂
    simp [gaussK₂, h]
  have hInv₁b : (Real.Gamma (1 - b))⁻¹ ≠ 0 := by
    intro h
    apply hK₂
    simp [gaussK₂, h]
  have hInvAc : (Real.Gamma (a - c + 1))⁻¹ ≠ 0 := by
    intro h
    apply hK₂
    simp [gaussK₂, h]
  have hInvBc : (Real.Gamma (b - c + 1))⁻¹ ≠ 0 := by
    intro h
    apply hK₂
    simp [gaussK₂, h]
  have hGamma₁a : Real.Gamma (1 - a) ≠ 0 := by
    intro h
    apply hInv₁a
    simp [h]
  have hGamma₁b : Real.Gamma (1 - b) ≠ 0 := by
    intro h
    apply hInv₁b
    simp [h]
  have hGammaAc : Real.Gamma (a - c + 1) ≠ 0 := by
    intro h
    apply hInvAc
    simp [h]
  have hGammaBc : Real.Gamma (b - c + 1) ≠ 0 := by
    intro h
    apply hInvBc
    simp [h]
  by_cases hd : d = 0
  · have hFactor : Real.Gamma (c - a) = 0 ∨ Real.Gamma (c - b) = 0 ∨
        Real.Gamma a = 0 ∨ Real.Gamma b = 0 := by
      dsimp [d] at hd
      rcases mul_eq_zero.mp hd with h | h
      · aesop
      · simp_all
    have hK₁ : gaussK₁ a b c = 0 := by
      rcases hFactor with h | h | h | h <;>
        simp [gaussK₁, h]
    have hden : Real.Gamma (2 - c) ^ 2 * Real.Gamma (c - a) * Real.Gamma (c - b) *
        Real.Gamma a * Real.Gamma b = 0 := by
      calc
        _ = Real.Gamma _ ^ 2 * d := by linarith
        _ = 0 := by simp_all
    have hratio : gaussCoefficientRatio a b c = 0 := by
      simp [gaussCoefficientRatio, hden]
    simp_all
  · have hGammaCa : Real.Gamma (c - a) ≠ 0 := by
      intro h
      apply hd
      simp [d, h]
    have hGammaCb : Real.Gamma (c - b) ≠ 0 := by
      intro h
      apply hd
      simp [d, h]
    have hGammaA : Real.Gamma a ≠ 0 := by
      intro h
      apply hd
      simp [d, h]
    have hGammaB : Real.Gamma b ≠ 0 := by
      intro h
      apply hd
      simp [d, h]
    dsimp [gaussCoefficientRatio, gaussK₁, gaussK₂]
    grind

end DOZZ.Proofs
