/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Gluing.Coefficient
public import DOZZ.ShiftEquations.Gluing.CoefficientAlgebra
public import DOZZ.Statements.Hypergeom.PlanarGaussConstant
public import DOZZ.Statements.FourPoint.FourPointT
import DOZZ.ShiftEquations.Rbar.Multiplier
import DOZZ.ShiftEquations.Reflection.RbarContinuity
import DOZZ.FourPoint.Diagonal.Assembly
import DOZZ.Hypergeom.ODE.SlitPlaneGluing

/-!
# The first structure shift at real points, from the unreflected fusion formula

For `γ/2 < α₁ < 2/γ` and `α₁ + α₂ + α₃ > 2Q + γ/2`, the unreflected formula
(`DOZZ.gammaHalf_full_unreflected_formula`) and the diagonal classification
(`DOZZ.degenerateFourPoint_diagonal_classification`, at `χ = γ/2`) express the degenerate four-point
function on two bases; the coefficients of `|F₊|²` agree:
`-μ G(γ²/2, γα₁) C(α₁ + γ/2) = ρ(a, b, c) C(α₁ - γ/2)`, where `G` is the planar Gauss constant and
`ρ` the Gauss coefficient ratio. With `ρ l(-γ²/4) l(γα₁/2) l(2 + γ²/4 - γα₁/2) = 𝒜(α₁)` this is the
first structure shift `C(α₁ + γ/2) = -𝒜(α₁) C(α₁ - γ/2)/(πμ)` ([KRV, Theorem 9.1]).
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs



/-- **The first structure shift at real points**, from the unreflected formula. -/
theorem firstShift_real_of_unreflected {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    X (M : Ω → Measure ℂ) {γ μ α₁ α₂ α₃ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hμ : 0 < μ) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hUnreflectedFormula : ∀ {H : ℂ → ℂ → ℂ → ℂ → ℂ}, IsGaussHypergeometricFamily H →
      let a := gaussParameterA γ (γ / 2) α₁ α₂ α₃
      let b := gaussParameterB γ (γ / 2) α₁ α₂ α₃
      let c := gaussParameterC γ (γ / 2) α₁
      ∀ z ∈ gaussCutPlane,
        fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z =
          structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ *
              ‖gaussFMinus H a b c z‖ ^ 2 +
            (-μ * (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re) *
              structureConstant P M γ μ (α₁ + γ / 2) α₂ α₃ *
                ‖gaussFPlus H a b c z‖ ^ 2)
    (h1 : γ / 2 < α₁) (h2 : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃) :
    (structureConstant P M γ μ (α₁ + γ / 2) α₂ α₃ : ℂ) =
      -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) (α₁ : ℂ) (α₂ : ℂ) (α₃ : ℂ) *
        (structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ : ℂ) := by
  have gaussParameterC_half_mem_window : 0 < gaussParameterC γ (γ / 2) α₁ ∧ gaussParameterC γ (γ / 2) α₁ < 1 := by
    unfold gaussParameterC
    have hQ : Q γ = 2 / γ + γ / 2 := rfl
    have : 0 < γ / 2 * (Q γ - α₁) := mul_pos (by positivity) (by linarith)
    have : γ / 2 * (Q γ - α₁) < γ / 2 * (Q γ - γ / 2) :=
      mul_lt_mul_of_pos_left (by linarith) (by positivity)
    have : γ / 2 * (Q γ - γ / 2) = 1 := by
      rw [hQ]
      field_simp
      ring
    constructor <;> linarith
  have unreflected_coefficient_real : (-μ * (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re) * structureConstant P M γ μ (α₁ + γ / 2) α₂ α₃ = gaussCoefficientRatio (gaussParameterA γ (γ / 2) α₁ α₂ α₃) (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) * structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ := by
    obtain ⟨H, hH⟩ := gauss_hypergeometric_exists
    have : Q γ = 2 / γ + γ / 2 := rfl
    have hc := gaussParameterC_half_mem_window
    have hK := second_coefficient_of_classification P M hH γ μ (γ / 2) α₁ α₂ α₃ _
      (complex_ne_int_of_mem_unit hc.1 hc.2) (degenerateFourPoint_diagonal_classification hH P X M γ μ (γ / 2) α₁ α₂ α₃ hγ hγ2 hμ (Or.inl rfl) (by linarith) hα₂ hα₃ hs hX hM) (by intro z hz; rw [← neg_div]; exact hUnreflectedFormula hH z hz)
    rw [hK]
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hK := unreflected_coefficient_real
  -- the three `l`-factors are real, finite and nonzero
  set x₁ : ℝ := γ * α₁ / 2 with hx₁
  have hx₁0 : γ ^ 2 / 4 < x₁ := by
    rw [hx₁]
    nlinarith
  have hx₁1 : x₁ < 1 := by
    rw [hx₁]
    have := mul_lt_mul_of_pos_left h2 hγ
    rw [show γ * (2 / γ) = 2 by field_simp] at this
    linarith
  have : 0 < γ ^ 2 / 4 := by positivity
  have : γ ^ 2 / 4 < 1 := by nlinarith
  have hl₁ : lFun (x₁ : ℂ) ≠ 0 := lFun_ne_zero
    (ofReal_ne_neg_nat_of_mem (Or.inr (Or.inl ⟨by linarith, hx₁1⟩)))
    (by
      rw [show (1 : ℂ) - x₁ = ((1 - x₁ : ℝ) : ℂ) by push_cast; ring]
      exact ofReal_ne_neg_nat_of_mem (Or.inr (Or.inl ⟨by linarith, by linarith⟩)))
  have hl₂ : lFun ((-(γ ^ 2 / 4) : ℝ) : ℂ) ≠ 0 := lFun_ne_zero
    (ofReal_ne_neg_nat_of_mem (Or.inl ⟨by linarith, by linarith⟩))
    (by
      rw [show (1 : ℂ) - ((-(γ ^ 2 / 4) : ℝ) : ℂ) = ((1 + γ ^ 2 / 4 : ℝ) : ℂ) by push_cast; ring]
      exact ofReal_ne_neg_nat_of_mem (Or.inr (Or.inr ⟨by linarith, by linarith⟩)))
  have hl₃ : lFun ((2 + γ ^ 2 / 4 - x₁ : ℝ) : ℂ) ≠ 0 := lFun_ne_zero
    (ofReal_ne_neg_nat_of_mem (Or.inr (Or.inr ⟨by linarith, by linarith⟩)))
    (by
      rw [show (1 : ℂ) - ((2 + γ ^ 2 / 4 - x₁ : ℝ) : ℂ) = ((-(1 + γ ^ 2 / 4 - x₁)) : ℝ) by
        push_cast; ring]
      exact ofReal_ne_neg_nat_of_mem (Or.inl ⟨by linarith, by linarith⟩))
  -- the planar Gauss constant in terms of the three factors
  have hG : (planarGaussConstant (γ ^ 2 / 2) (γ * α₁) : ℂ) =
      (Real.pi : ℂ) / (lFun (x₁ : ℂ) * lFun ((-(γ ^ 2 / 4) : ℝ) : ℂ) *
        lFun ((2 + γ ^ 2 / 4 - x₁ : ℝ) : ℂ)) := by
    unfold planarGaussConstant
    rw [hx₁]
    congr 3 <;> push_cast <;> ring_nf
  have hGre : ((planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re : ℂ) =
      planarGaussConstant (γ ^ 2 / 2) (γ * α₁) := by
    rw [hG, lFun_ofReal, lFun_ofReal, lFun_ofReal]
    norm_cast
  -- the Gamma identity `ρ l l l = 𝒜`
  have hA := gaussCoefficientRatio_mul_eq_shiftCoeffA_half (α₂ := α₂) (α₃ := α₃) hγ
    (z := α₁) (ne_of_lt (gaussParameterC_half_mem_window).2)
  rw [(show lFun (-((γ / 2 : ℝ) : ℂ) ^ 2) * lFun (((γ / 2 : ℝ) : ℂ) * α₁) * lFun (2 + ((γ / 2 : ℝ) : ℂ) ^ 2 - ((γ / 2 : ℝ) : ℂ) * α₁) = lFun (x₁ : ℂ) * lFun ((-(γ ^ 2 / 4) : ℝ) : ℂ) * lFun ((2 + γ ^ 2 / 4 - x₁ : ℝ) : ℂ) by rw [(show -((γ / 2 : ℝ) : ℂ) ^ 2 = ((-(γ ^ 2 / 4) : ℝ) : ℂ) by push_cast; ring), (show (2 : ℂ) + ((γ / 2 : ℝ) : ℂ) ^ 2 - ((γ / 2 : ℝ) : ℂ) * α₁ = ((2 + γ ^ 2 / 4 - x₁ : ℝ) : ℂ) by rw [hx₁]; push_cast; ring), (show ((γ / 2 : ℝ) : ℂ) * α₁ = (x₁ : ℂ) by rw [hx₁]; push_cast; ring)]; ring)] at hA
  -- assemble
  have hKc := congrArg (fun r : ℝ => (r : ℂ)) hK
  simp only [Complex.ofReal_mul, Complex.ofReal_neg] at hKc
  rw [hGre, hG] at hKc
  have := Complex.ofReal_ne_zero.mpr hμ.ne'
  have := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  rw [show shiftCoeffA γ (γ / 2) (α₁ : ℂ) (α₂ : ℂ) (α₃ : ℂ) =
    shiftCoeffA γ ((γ / 2 : ℝ) : ℂ) α₁ α₂ α₃ by push_cast; rfl, ← hA]
  have hL := mul_ne_zero (mul_ne_zero hl₁ hl₂) hl₃
  generalize lFun (x₁ : ℂ) * lFun ((-(γ ^ 2 / 4) : ℝ) : ℂ) * lFun ((2 + γ ^ 2 / 4 - x₁ : ℝ) : ℂ) = L
    at hL hKc ⊢
  generalize (gaussCoefficientRatio (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
    (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) : ℂ) = ρ at hKc ⊢
  generalize (structureConstant P M γ μ (α₁ + γ / 2) α₂ α₃ : ℂ) = Cp at hKc ⊢
  generalize (structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ : ℂ) = Cm at hKc ⊢
  rw [(show Cp = (-(μ : ℂ) * ((Real.pi : ℂ) / L) * Cp) * (-L / ((μ : ℂ) * Real.pi)) by field_simp), hKc]
  field_simp

end DOZZ.Proofs

end
