module

public import NearlyMinimax.HighFrameLegality
public import NearlyMinimax.SpatialCardinalCovariance

@[expose] public section

/-! Exact bridge from the manuscript's finite total-degree coefficient
frame to the genuine polynomial fields used in original-model legality. -/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {d D : ℕ} (c : HighFrameVector d D)

theorem frameCoefficientL1_sum_monomial_le {I : Type*} [Fintype I]
    (e : I → Fin d →₀ ℕ) (c : I → ℝ) :
    frameCoefficientL1 (∑ i, MvPolynomial.monomial (e i) (c i)) ≤ ∑ i, |c i| := by
  classical
  calc
    _ ≤ ∑ β ∈ (∑ i, MvPolynomial.monomial (e i) (c i)).support, ∑ i, |(MvPolynomial.monomial (e i) (c i)).coeff β| := by
      apply Finset.sum_le_sum
      intro β hβ
      simpa using norm_sum_le Finset.univ
        (fun i => (MvPolynomial.monomial (e i) (c i)).coeff β)
    _ = _ :=
      Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [MvPolynomial.coeff_monomial, apply_ite abs, abs_zero]
      rw [Finset.sum_ite_eq]
      bound

def highFramePolynomial :
    MvPolynomial (Fin d) ℝ :=
  ∑ γ, MvPolynomial.monomial (polynomialBoxExponent γ.val) (c γ)

theorem highFramePolynomial_coefficientL1_le :
    frameCoefficientL1 (highFramePolynomial c) ≤ ∑ γ, |c γ| :=
  frameCoefficientL1_sum_monomial_le _ _

theorem highFramePolynomial_scaled_eval
    (x : Covariate d) :
    MvPolynomial.eval x (frameScaledPolynomial (highFramePolynomial c)) =
      ∑ γ, c γ * highFrameFeature x γ := by
  classical
  rw [frameScaledPolynomial_eval]
  simp only [highFramePolynomial, map_sum, MvPolynomial.eval_monomial,
    highFrameFeature]
  simp

end NearlyMinimax
