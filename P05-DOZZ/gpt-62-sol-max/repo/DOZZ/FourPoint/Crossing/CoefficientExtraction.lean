/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Crossing.ConnectionDet
public import DOZZ.FourPoint.Crossing.ConnectionRatio
import Mathlib.Tactic
public import DOZZ.FourPoint.Crossing.DiagonalUniqueness
public import DOZZ.Hypergeom.ConnectionDiagonalCoefficients

/-! # Crossing from the two diagonal coefficients

This is finite matrix algebra on the source's physical Gauss intervals. The
hypotheses describe two diagonal quadratic forms related by the literal connection
matrix; the conclusion identifies their zero-channel and one-channel coefficients.
-/

public section
namespace DOZZ.Proofs

/-- The zero-channel first coefficient is the exact l-ratio times the
one-channel second coefficient. -/
theorem crossing_diagonal_coefficient_extraction (a b c d₀ d₁ E : ℝ)
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hc1 : c < 1)
    (hδ : 0 < c - a - b) (hδ1 : c - a - b < 1)
    (hcross : d₀ * gaussConnectionReal₁₁ a b c * gaussConnectionReal₁₂ a b c +
      d₁ * gaussConnectionReal₂₁ a b c * gaussConnectionReal₂₂ a b c = 0)
    (hE : E = d₀ * gaussConnectionReal₁₂ a b c ^ 2 + d₁ * gaussConnectionReal₂₂ a b c ^ 2) :
    d₀ = (lR a * lR b / (lR c * lR (a + b - c))) * E := by
  let u := gaussConnectionReal₁₁ a b c
  let v := gaussConnectionReal₁₂ a b c
  let w := gaussConnectionReal₂₁ a b c
  let x := gaussConnectionReal₂₂ a b c
  have hb := ha.trans hab
  have hc := hb.trans hbc
  have ha1 := hab.trans (hbc.trans hc1)
  have hb1 := hbc.trans hc1
  have hw : w ≠ 0 := by
    dsimp [w, gaussConnectionReal₂₁]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero
      (Real.Gamma_pos_of_pos (by linarith only [hc1])).ne'
      (Real.Gamma_pos_of_pos hδ).ne')
      (inv_ne_zero (Real.Gamma_pos_of_pos (sub_pos.mpr ha1)).ne'))
      (inv_ne_zero (Real.Gamma_pos_of_pos (sub_pos.mpr hb1)).ne')
  have hΓneg : Real.Gamma (a + b - c) ≠ 0 := Real.Gamma_ne_zero
    (real_ne_neg_nat_of_frac (k := -1) (by push_cast; linarith only [hδ1])
      (by push_cast; linarith only [hδ]))
  have hv : v ≠ 0 := by
    dsimp [v, gaussConnectionReal₁₂]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Real.Gamma_pos_of_pos hc).ne' hΓneg)
      (inv_ne_zero (Real.Gamma_pos_of_pos ha).ne'))
      (inv_ne_zero (Real.Gamma_pos_of_pos hb).ne')
  have hdet  :=
    crossing_connection_det_real a b c (unit_interval_ne_int hc hc1) (unit_interval_ne_int hδ hδ1)
  have hdet0 : u * x - v * w ≠ 0 := by
    rw [hdet]
    exact div_ne_zero (by linarith only [hc1]) hδ.ne'
  have hex := dual_connection_first_seed_scalar d₀ d₁ u v w x hcross hw hv hdet0
  rw [← hE, hdet] at hex
  have hratio := crossing_connection_first_ratio a b c ha ha1 hb hb1 hc hc1 hδ hδ1
  rw [hratio] at hex
  exact hex

/-- Compare two diagonal expressions for a reduced four-point function. -/
theorem crossing_diagonal_transfer {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b c d e₀ e₁ : ℝ) {T : ℂ → ℝ}
    (hc : ∀ n : ℤ, c ≠ (n : ℝ)) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℝ))
    (hK : gaussK₂ a b c ≠ 0)
    (hzero : ∀ z ∈ gaussCutPlane, T z = d * (‖gaussFMinus H a b c z‖ ^ 2 +
      gaussCoefficientRatio a b c * ‖gaussFPlus H a b c z‖ ^ 2))
    (hone : ∀ z ∈ gaussCutPlane, T z = e₀ * ‖gaussGMinus H a b c z‖ ^ 2 +
      e₁ * ‖gaussGPlus H a b c z‖ ^ 2) :
    let d₁ := d * gaussCoefficientRatio a b c
    let u := gaussConnectionReal₁₁ a b c
    let v := gaussConnectionReal₁₂ a b c
    let w := gaussConnectionReal₂₁ a b c
    let x := gaussConnectionReal₂₂ a b c
    d * u * v + d₁ * w * x = 0 ∧
      e₀ = d * u ^ 2 + d₁ * w ^ 2 ∧ e₁ = d * v ^ 2 + d₁ * x ^ 2 := by
  intro d₁ u v w x
  have hratio := gaussCoefficientRatio_mul_K₂_add_K₁_eq_zero a b c hK
  have hconstraint : gaussK₁ a b c * d + gaussK₂ a b c * d₁ = 0 := by
    dsimp [d₁]
    linear_combination d * hratio
  have hcross : d * u * v + d₁ * w * x = 0 := by
    dsimp only [u, v, w, x]
    rw [gaussConnectionReal_cross, hconstraint, mul_zero]
  have htransfer := gauss_diagonal_one_basis_of_constraint hH a b c d d₁ hc hδ hconstraint
  have h := crossing_one_channel_coefficients_unique hH a b c e₀ e₁
    (d * u ^ 2 + d₁ * w ^ 2) (d * v ^ 2 + d₁ * x ^ 2) hδ (fun z hz => by
    dsimp only [u, v, w, x]
    rw [← hone z hz, ← htransfer z hz, hzero z hz]
    dsimp [d₁]
    ring)
  exact ⟨hcross, h.1, h.2⟩

end DOZZ.Proofs
