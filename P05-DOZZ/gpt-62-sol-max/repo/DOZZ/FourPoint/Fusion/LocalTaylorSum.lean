/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.LocalSecondLimit
public import DOZZ.FourPoint.Fusion.NormalizedLittleO

/-! # Summing the three local Taylor contributions -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The limiting moving inverse expectation is exactly the moment in
`gammaHalfRootedCoefficient`. -/
private theorem fusion_local_inverse_coefficient_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ s : ℝ) :
    (∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ 1 0 (M ω) ^ s ∂P) =
      ∫⁻ ω, gammaHalfRootedMass γ α₁ α₂ α₃ M ω ^ s ∂P := by
  apply lintegral_congr_ae
  filter_upwards [fusionMovingMass_eq_rooted_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ 1 0] with ω hω
  simpa only [mul_zero, gammaHalfRootedMass] using congrArg (fun a : ℝ≥0∞ => a ^ s) hω

/-- The pure contribution, its conjugate, and the mixed contribution sum to `-p A`. -/
theorem fusionLocalOneRooted_normalized_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hlo : γ / 2 < α₁) (hsq : 2 < γ ^ 2) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ) (hp : 0 ≤ p) :
    Tendsto (fun z : ℂ =>
      (fusionLocalR1 P M γ α₁ α₂ α₃ p z + fusionLocalR2 P M γ α₁ α₂ α₃ p z +
        star (fusionLocalR1 P M γ α₁ α₂ α₃ p z)) / (‖z‖ ^ (γ * (Q γ - α₁)) : ℝ))
      (nhdsWithin 0 {0}ᶜ) (nhds ((-p * gammaHalfRootedCoefficient P M γ α₁ α₂ α₃ p : ℝ) : ℂ)) := by
  obtain ⟨hk, hβ, hβ2, hβlin, _, _⟩ := fusion_taylor_parameters γ α₁ hγ hlo hsq hα₁
  let k := γ ^ 2 / 2
  let β := γ * α₁
  let q := γ ^ 2 / 4
  let d := k - β + 2
  let W := ∫ y : ℂ, planarWirtingerKernel k β 1 y
  let J := ∫ y : ℂ, planarMixedKernel k β 1 y
  let A := (planarGaussConstant k β).re
  let E := (∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ 1 0 (M ω) ^ (-p - 1) ∂P).toReal
  have hq : k / 2 = q := by dsimp [k, q]; ring
  have hd : 2 + k - β = d := by dsimp [d]; ring
  have hW := (planar_wirtinger_integral k β hk hβ hβ2 1 (by norm_num)).2
  have hJ := (planar_mixed_integral k β hk hβ hβ2 1 (by norm_num)).2
  simp only [norm_one, Real.one_rpow, one_pow, div_one, Complex.ofReal_one, mul_one,
    hq, hd] at hW hJ
  rw [fusion_planarGauss_real k β hk hβ hβ2 hβlin] at hW hJ
  change (q : ℂ) * ↑(q - 1) * W = ↑(d / 2) * ↑(d / 2 - 1) * (A : ℂ) at hW
  change (↑(q ^ 2 * J) : ℂ) = ↑((d / 2) ^ 2 : ℝ) * (A : ℂ) at hJ
  have hsW := congrArg star hW
  have hs (r : ℝ) : star (r : ℂ) = (r : ℂ) := by simp
  simp only [star_mul, hs] at hsW
  have h1 := fusionLocalSecond_normalized_tendsto false P X hX γ hγ hγ2 M hM α₁ α₂ α₃
    hlo hsq hα₁ hα₂ hα₃ p hp
  have h2 := fusionLocalSecond_normalized_tendsto true P X hX γ hγ hγ2 M hM α₁ α₂ α₃
    hlo hsq hα₁ hα₂ hα₃ p hp
  have h := (h1.add h2).add h1.star
  have he : k - β + 1 = d - 1 := by dsimp [d]; ring
  have hb : β < k + 1 := hβlin
  have hd1 : d - 1 ≠ 0 := by dsimp only [d]; linarith only [hb]
  have hd0 : d ≠ 0 := by dsimp only [d]; linarith only [hb]
  have hc : ((-p * q * (q - 1) : ℝ) : ℂ) * (↑(1 / ((d - 1) * d)) * (W * (E : ℂ))) +
      ((-2 * p * q ^ 2 : ℝ) : ℂ) * (↑(1 / ((d - 1) * d)) * ((J : ℂ) * (E : ℂ))) +
      ((-p * q * (q - 1) : ℝ) : ℂ) * (↑(1 / ((d - 1) * d)) * (star W * (E : ℂ))) =
      ((-p * A * E : ℝ) : ℂ) := by
    push_cast at hW hJ hsW ⊢
    have hd1' : (d : ℂ) - 1 ≠ 0 := by exact_mod_cast hd1
    have hd0' : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
    field_simp
    linear_combination -(p : ℂ) * E * (hW + hsW + 2 * hJ)
  have hroot : A * E = gammaHalfRootedCoefficient P M γ α₁ α₂ α₃ p := by
    unfold E
    rw [fusion_local_inverse_coefficient_eq P X hX γ hγ hγ2 M hM α₁ α₂ α₃ (-p - 1)]
    rfl
  have hr : -p * A * E = -p * gammaHalfRootedCoefficient P M γ α₁ α₂ α₃ p := by
    rw [mul_assoc, hroot]
  rw [hr] at hc
  simp only [fusionSecondCoeff, fusionPlanarSecond, Bool.false_eq_true, ite_false, ite_true,
    star_mul', star_div₀, hs, integral_complex_ofReal, ← add_div,
    show γ ^ 2 / 2 - γ * α₁ + 1 = d - 1 from he] at h
  rwa [hc] at h

end DOZZ.Proofs
