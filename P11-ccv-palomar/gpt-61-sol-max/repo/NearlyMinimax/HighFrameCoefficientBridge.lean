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

theorem frameCoefficientL1_sum_monomial_le {d : ℕ} {I : Type*} [Fintype I]
    (e : I → Fin d →₀ ℕ) (c : I → ℝ) :
    frameCoefficientL1 (∑ i, MvPolynomial.monomial (e i) (c i)) ≤ ∑ i, |c i| := by
  classical
  let P  := ∑ i, MvPolynomial.monomial (e i) (c i)
  
  calc
    _ ≤ ∑ β ∈ P.support, ∑ i, |(MvPolynomial.monomial (e i) (c i)).coeff β| := by
      apply Finset.sum_le_sum
      intro β hβ
      
      rw [MvPolynomial.coeff_sum]
      simpa only [Real.norm_eq_abs] using norm_sum_le Finset.univ
        (fun i => (MvPolynomial.monomial (e i) (c i)).coeff β)
    _ = ∑ i, ∑ β ∈ P.support, |(MvPolynomial.monomial (e i) (c i)).coeff β| :=
      Finset.sum_comm
    _ ≤ ∑ i, |c i| := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [MvPolynomial.coeff_monomial, apply_ite abs, abs_zero]
      rw [Finset.sum_ite_eq]
      split_ifs
      · exact le_rfl
      · exact abs_nonneg _

def highFramePolynomial {d D } (c : HighFrameIndex d D → ℝ)  :=
  ∑ γ, MvPolynomial.monomial (polynomialBoxExponent γ.val) (c γ)

section
variable {d D : ℕ} (c : HighFrameIndex d D → ℝ)

theorem highFramePolynomial_coefficientL1_le  :
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
  norm_num
end


end NearlyMinimax
