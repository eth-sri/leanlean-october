module

public import NearlyMinimax.HighFrameLegality
public import NearlyMinimax.SpatialCardinalCovariance
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Exact bridge from the manuscript's finite total-degree coefficient
frame to the genuine polynomial fields used in original-model legality. -/
open MvPolynomial
𝚪
𝚨
𝚩
𝚰

𝗇 𝔄 MvPolynomial.monomial (e i) $ c i
theorem frameCoefficientL1_sum_monomial_le [Fintype I]
    (e : I → 𝖨₁) (c : 𝗦₂) :
    frameCoefficientL1 (∑ i, 𝔄) ≤ ∑ i, |c i| := by
  classical
  let P := ∑ i, 𝔄
  calc
    _ ≤ ∑ β ∈ P.support, ∑ i, |(𝔄).coeff β| := by
      apply Finset.sum_le_sum
      intro β hβ
      rw [MvPolynomial.coeff_sum]
      simpa only [Real.norm_eq_abs] using norm_sum_le Finset.univ
         fun i => (𝔄).coeff β
    _ = ∑ i, ∑ β ∈ P.support, |(𝔄).coeff β| :=
      Finset.sum_comm
    _ ≤ ∑ i, |c i| := by
      apply Finset.sum_le_sum
      simp only [MvPolynomial.coeff_monomial, apply_ite abs]
      aesop

def highFramePolynomial (c : 𝙮 → ℝ) :
    𝙣 :=
  ∑ γ, MvPolynomial.monomial (polynomialBoxExponent γ.val) (c γ)

section

variable (c : 𝙮 → ℝ)

theorem highFramePolynomial_coefficientL1_le :
    frameCoefficientL1 (highFramePolynomial c) ≤ ∑ γ, |c γ| :=
  frameCoefficientL1_sum_monomial_le ..

theorem highFramePolynomial_scaled_eval (x : Covariate d) :
    MvPolynomial.eval x (frameScaledPolynomial $ highFramePolynomial c ) =
      ∑ γ, c γ * highFrameFeature x γ := by
  classical
  rw [frameScaledPolynomial_eval]
  simp only [highFramePolynomial, map_sum, MvPolynomial.eval_monomial,
    highFrameFeature]
  simp
