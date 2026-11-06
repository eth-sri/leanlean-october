module
public import NearlyMinimax.HighFrameCoefficientBridge
public import NearlyMinimax.CardinalSeparatedComposition
@[expose] public section
noncomputable section
open MvPolynomial MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {d D n : ℕ}
theorem frameCoefficientL1_mul  (P Q : MvPolynomial (Fin d) ℝ) :
    frameCoefficientL1 (P * Q) ≤ frameCoefficientL1 P * frameCoefficientL1 Q := by
  have hP  := P.as_sum.trans (Finset.sum_coe_sort P.support
      (fun β => monomial β (P.coeff β))).symm
  have hQ  := Q.as_sum.trans (Finset.sum_coe_sort Q.support
      (fun β => monomial β (Q.coeff β))).symm
  have hprod : P * Q = ∑ β : P.support × Q.support,
      monomial (β.1.val + β.2.val) (P.coeff β.1.val * Q.coeff β.2.val) := by
    calc
      P * Q = (∑ β : P.support, monomial β.val (P.coeff β.val)) *
          (∑ β : Q.support, monomial β.val (Q.coeff β.val)) := congrArg₂ (· * ·) hP hQ
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
    _ = frameCoefficientL1 P * frameCoefficientL1 Q := by
      rw [← Finset.sum_mul Finset.univ
        (fun β : P.support => |P.coeff β.val|) (frameCoefficientL1 Q), Finset.sum_coe_sort P.support (fun β => |P.coeff β|)]
      rfl
theorem frameCoefficientL1_one  :
    frameCoefficientL1 (1 : MvPolynomial (Fin d) ℝ) = 1 := by
  simp [frameCoefficientL1, MvPolynomial.support_one]
theorem frameCoefficientL1_prod   (s )
    (P : I → MvPolynomial (Fin d) ℝ) :
    frameCoefficientL1 (∏ i ∈ s, P i) ≤ ∏ i ∈ s, frameCoefficientL1 (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [frameCoefficientL1_one]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (frameCoefficientL1_mul _ _).trans
      (mul_le_mul_of_nonneg_left ih (frameCoefficientL1_nonneg _))
theorem frameCoefficientL1_coeff_sum_le  (P : MvPolynomial (Fin d) ℝ)
    (s ) :
    (∑ β ∈ s, |P.coeff β|) ≤ frameCoefficientL1 P := by
  calc
    _ = ∑ β ∈ s ∩ P.support, |P.coeff β| := by
      symm
      apply Finset.sum_subset (Finset.inter_subset_left)
      intro β hβ hnot
      simp [MvPolynomial.notMem_support_iff.mp (by intro hm; exact hnot (Finset.mem_inter.mpr ⟨hβ, hm⟩))]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun _ _ _ => abs_nonneg _)
theorem highFrameCoefficients_sum_abs_le  (P : MvPolynomial (Fin d) ℝ) :
    (∑ γ : HighFrameIndex d D, |highFrameCoefficients P γ|) ≤ frameCoefficientL1 P := by
  let e : HighFrameIndex d D → Fin d →₀ ℕ := fun γ => polynomialBoxExponent γ.val
  have he : Function.Injective e := by
    intro γ δ h
    exact Subtype.ext (polynomial_box_exponent_injective h)
  calc
    _ = ∑ β ∈ Finset.univ.image e, |P.coeff β| := by
      rw [Finset.sum_image]
      · rfl
      · intro γ _ δ _ h
        exact he h
    _ ≤ _ := frameCoefficientL1_coeff_sum_le _ _
def spatialAffineExponent  (z : Fin d × Bool) : Fin d →₀ ℕ :=
  if z.2 then 0 else Finsupp.single z.1 1
def spatialAffineCoefficient  (x y : Covariate d) (z : Fin d × Bool) : ℝ :=
  if z.2 then (y z.1 - x z.1) * y z.1 else -8 * (y z.1 - x z.1)
theorem spatial_cardinal_affine_coefficient_l1_square_le  (x y : Covariate d)
    (hy : ∀ r, |y r| ≤ 2) :
    (frameCoefficientL1 (spatialCardinalAffine x y)) ^ 2 ≤ 100 * ↑d * spatialSquaredDistance x y := by
  have h_spatial_cardinal_affine_coefficient_l1_le : frameCoefficientL1 (spatialCardinalAffine x y) ≤ 10 * ∑ r, |y r - x r| := by
    have h_spatial_cardinal_affine_monomial_sum : spatialCardinalAffine x y =
        ∑ z : Fin d × Bool, MvPolynomial.monomial (spatialAffineExponent z) (spatialAffineCoefficient x y z) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Fintype.sum_bool]
      simp only [spatialAffineExponent, spatialAffineCoefficient, Bool.false_eq_true, ite_false, ite_true]
      rw [← MvPolynomial.C_apply, ← MvPolynomial.C_mul_X_eq_monomial, show (-8 ) * (y r - x r) = -(8 * (y r - x r)) by ring, map_neg]
      ring
    rw [h_spatial_cardinal_affine_monomial_sum]
    apply (frameCoefficientL1_sum_monomial_le _ _).trans
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    rw [Fintype.sum_bool]
    simp only [spatialAffineCoefficient, Bool.false_eq_true, ite_false, ite_true, abs_mul]
    norm_num only [abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 8 by norm_num)]
    have := mul_le_mul_of_nonneg_left (hy r) (abs_nonneg (y r - x r))
    linarith
  have := (sq_le_sq₀ (frameCoefficientL1_nonneg _) (by positivity)).mpr (h_spatial_cardinal_affine_coefficient_l1_le)
  have hsum := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
    (f := fun r => |y r - x r|)
  simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at hsum
  change (∑ r, |y r - x r|) ^ 2 ≤ d * spatialSquaredDistance x y at hsum
  nlinarith
def spatialMatrixL1  (A : HighFrameIndex d D → HighFrameIndex d D → ℝ) : ℝ :=
  ∑ β, ∑ β', |A β β'|
theorem spatial_matrix_l1_nonnegative  (A : HighFrameIndex d D → HighFrameIndex d D → ℝ) :
    0 ≤ spatialMatrixL1 A := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
theorem spatial_cardinal_scale_nonnegative  (i : Fin n) (lam : ℝ)
    (U : Fin n → Covariate d) (t : SpatialScaleVector i) (ht : t ∈ Ici 0) :
    0 ≤ spatialCardinalScale lam (spatialScaleExtend i t) U i := by
  rw [spatial_cardinal_scale_product]
  exact Finset.prod_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (ht j) (sq_nonneg _)) (Real.exp_pos _).le)
end NearlyMinimax
