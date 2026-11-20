module

public import NearlyMinimax.HighFrameCoefficientBridge


@[expose] public section

/-! Coefficient norm estimates for the actual polynomial frame. These are
algebraic bounds on polynomial coefficients and do not assume an envelope. -/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {d : ℕ} {I : Type*} {D : ℕ} (P Q : MvPolynomial (Fin d) ℝ)

theorem frameCoefficientL1_mul :
    frameCoefficientL1 (P * Q) ≤ frameCoefficientL1 P * frameCoefficientL1 Q := by
  classical
  have hP  := P.as_sum.trans (Finset.sum_coe_sort P.support
      (fun β => monomial β (P.coeff β))).symm
  have hQ  := Q.as_sum.trans (Finset.sum_coe_sort Q.support
      (fun β => monomial β (Q.coeff β))).symm
  have hprod : P * Q = ∑ β : P.support × Q.support,
      monomial (β.1.val + β.2.val) (P.coeff β.1.val * Q.coeff β.2.val) := by
    calc
      _ = _ := congrArg₂ _ hP hQ
      _ = _ := by
        simp_rw [Finset.sum_mul, Finset.mul_sum, monomial_mul_monomial]
        rw [Fintype.sum_prod_type]
  rw [hprod]
  apply (frameCoefficientL1_sum_monomial_le _ _).trans_eq
  simp_rw [Fintype.sum_prod_type, abs_mul]
  calc
    _ = ∑ β : P.support, |P.coeff β.val| * frameCoefficientL1 Q := by
      apply Finset.sum_congr rfl
      intro β _
      rw [← Finset.mul_sum Finset.univ
        (fun γ : Q.support => |Q.coeff γ.val|) |P.coeff β.val|, Finset.sum_coe_sort Q.support (fun γ => |Q.coeff γ|)]
      rfl
    _ = _ := by
      rw [← Finset.sum_mul Finset.univ
        (fun β : P.support => |P.coeff β.val|) (frameCoefficientL1 Q), Finset.sum_coe_sort P.support (fun β => |P.coeff β|)]
      rfl

theorem frameCoefficientL1_one :
    frameCoefficientL1 (1 : MvPolynomial (Fin d) ℝ) = 1 := by
  simp [frameCoefficientL1]

theorem frameCoefficientL1_prod (s : Finset I)
    (P : I → MvPolynomial (Fin d) ℝ) :
    frameCoefficientL1 (∏ i ∈ s, P i) ≤ ∏ i ∈ s, frameCoefficientL1 (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [frameCoefficientL1_one]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (frameCoefficientL1_mul _ _).trans
      (mul_le_mul_of_nonneg_left ih (frameCoefficientL1_nonneg _))

theorem frameCoefficientL1_coeff_sum_le
    (s : Finset (Fin d →₀ ℕ)) :
    (∑ β ∈ s, |P.coeff β|) ≤ frameCoefficientL1 P := by
  classical
  calc
    _ = _ := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      aesop
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun _ _ _ => abs_nonneg _)

theorem highFrameCoefficients_sum_abs_le :
    (∑ γ : HighFrameIndex d D, |highFrameCoefficients P γ|) ≤ frameCoefficientL1 P := by
  classical
  let e : HighFrameIndex d D → Fin d →₀ ℕ := fun γ => polynomialBoxExponent γ.val
  have he : Function.Injective e := fun γ δ h => Subtype.ext (polynomial_box_exponent_injective h)
  calc
    _ = _ := by
      rw [Finset.sum_image]
      · rfl
      · intro γ _ δ _ h
        exact he h
    _ ≤ _ := frameCoefficientL1_coeff_sum_le _ _

end NearlyMinimax
