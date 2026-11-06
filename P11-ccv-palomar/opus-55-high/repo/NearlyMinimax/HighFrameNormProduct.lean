module

public import NearlyMinimax.HighFrameCoefficientBridge
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Coefficient norm estimates for the actual polynomial frame. These are
algebraic bounds on polynomial coefficients and do not assume an envelope. -/
open MvPolynomial
𝚪
𝚨
𝚩
𝚭

𝗇 𝔄 𝙣
𝗇 𝔅 P * Q
𝗃 𝔇 fun β => monomial β $ ἀ β
theorem frameCoefficientL1_mul (P Q : 𝔄) :
    frameCoefficientL1 𝔅 ≤ frameCoefficientL1 P * frameCoefficientL1 Q := by
  classical
  have hP := P.as_sum.trans (Finset.sum_coe_sort P.support
      𝔇 P.coeff).symm
  have hQ := Q.as_sum.trans (Finset.sum_coe_sort Q.support
      𝔇 Q.coeff).symm
  have hprod : 𝔅 = ∑ β : P.support × Q.support,
      monomial (β.1.val + β.2.val) (P.coeff β.1.val * Q.coeff β.2.val) := by
    calc
      𝔅 = (∑ β : P.support, monomial β.val (P.coeff β.val)) *
           ∑ β : Q.support, monomial β.val (Q.coeff β.val) := congrArg₂ (· * ·) hP hQ
      𝘿 := by
        simp_rw [Finset.sum_mul, Finset.mul_sum, monomial_mul_monomial]
        rw [Fintype.sum_prod_type]
  rw [hprod]
  apply (frameCoefficientL1_sum_monomial_le ..).trans_eq
  simp_rw [Fintype.sum_prod_type, abs_mul]
  calc
    _ = ∑ β : P.support, |P.coeff β.val| * frameCoefficientL1 Q := by
      apply Finset.sum_congr rfl
      intro β _
      rw [← Finset.mul_sum Finset.univ
        (fun γ : Q.support => |Q.coeff γ.val|) |P.coeff β.val|]
      rw [Finset.sum_coe_sort Q.support fun γ => |Q.coeff γ| ]
      rfl
    _ = frameCoefficientL1 P * frameCoefficientL1 Q := by
      rw [← Finset.sum_mul Finset.univ
        (fun β : P.support => |P.coeff β.val|) $ frameCoefficientL1 Q ]
      rw [Finset.sum_coe_sort P.support fun β => |P.coeff β| ]
      rfl

theorem frameCoefficientL1_one :
    frameCoefficientL1 (1 : 𝔄) = 1 := by
  classical
  simp [frameCoefficientL1]

theorem frameCoefficientL1_prod s
    (P : I → 𝔄) :
    frameCoefficientL1 (∏ i ∈ s, P i) ≤ ∏ i ∈ s, frameCoefficientL1 (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [frameCoefficientL1_one]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (frameCoefficientL1_mul ..).trans
      $ mul_le_mul_of_nonneg_left ih $ frameCoefficientL1_nonneg _

theorem frameCoefficientL1_coeff_sum_le (P : 𝔄)
    s :
     ∑ β ∈ s, |P.coeff β| ≤ frameCoefficientL1 P := by
  classical
  calc
    _ = ∑ β ∈ s ∩ P.support, |P.coeff β| := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      simp_all
    𝖦 := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
       fun _ _ _ => abs_nonneg _

theorem highFrameCoefficients_sum_abs_le P :
     ∑ γ : 𝙮, |highFrameCoefficients P γ| ≤ frameCoefficientL1 P := by
  classical
  let e : 𝙮 → 𝖨₁ := fun γ => polynomialBoxExponent γ.val
  have he : Function.Injective e := by
    intro γ δ h
    exact Subtype.ext $ polynomial_box_exponent_injective h
  calc
    _ = ∑ β ∈ Finset.univ.image e, |P.coeff β| := by
      aesop
    𝖦 := frameCoefficientL1_coeff_sum_le ..
