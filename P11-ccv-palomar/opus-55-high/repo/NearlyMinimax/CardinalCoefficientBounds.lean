module

public import NearlyMinimax.HighFrameCoefficientBridge
public import NearlyMinimax.CardinalSeparatedComposition
public import NearlyMinimax.HighFrameNormProduct
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual coefficient bounds for the division-free spatial cardinal
polynomials, including collisions. -/
𝛄
𝚪
𝚨
𝚩
𝚱

𝗇 𝔔 Fin d × Bool
def spatialAffineExponent (z : 𝔔) : 𝖨₁ :=
  if z.2 then 0 else Finsupp.single z.1 1

𝗇 𝔑 y z.1 - x z.1
def spatialAffineCoefficient (x y : Covariate d) (z : 𝔔) : ℝ :=
  if z.2 then 𝔑 * y z.1 else -8 * 𝔑

𝗇 𝔇 𝗵₂
𝗇 𝔒 spatialCardinalAffine x y
theorem spatial_cardinal_affine_monomial_sum x y :
    𝔒 =
      ∑ z : 𝔔, MvPolynomial.monomial (spatialAffineExponent z) (spatialAffineCoefficient x y z) := by
  classical
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Fintype.sum_bool]
  simp only [spatialAffineExponent, spatialAffineCoefficient, Bool.false_eq_true, ite_false, ite_true]
  rw [← MvPolynomial.C_apply, ← MvPolynomial.C_mul_X_eq_monomial]
  rw [show -8 * 𝔇 = -(8 * 𝔇) by ring, map_neg]
  ring

theorem spatial_cardinal_affine_coefficient_l1_le (x y : Covariate d)
    (hy : ∀ r, |y r| ≤ 2) :
    frameCoefficientL1 𝔒 ≤ 10 * ∑ r, |𝔇| := by
  rw [spatial_cardinal_affine_monomial_sum]
  apply (frameCoefficientL1_sum_monomial_le ..).trans
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  rw [Fintype.sum_bool]
  simp only [spatialAffineCoefficient, Bool.false_eq_true, ite_false, ite_true, abs_mul]
  norm_num only [abs_neg, abs_of_nonneg $ show 𝙋 ≤ 8 by norm_num ]
  have h := mul_le_mul_of_nonneg_left (hy r) $ abs_nonneg 𝔇
  linarith

𝗇 𝔏 100 * d
𝗃 𝔚 frameCoefficientL1 ἀ ^ 2
/-- The actual affine coefficient norm vanishes at a collision and is
controlled by squared spatial distance everywhere. -/
theorem spatial_cardinal_affine_coefficient_l1_square_le (x y : Covariate d)
    (hy : ∀ r, |y r| ≤ 2) :
    𝔚 𝔒 ≤ 𝔏 * 𝖬₁ := by
  have hs := (sq_le_sq₀ (frameCoefficientL1_nonneg _) 𝖠₃ ).mpr $ spatial_cardinal_affine_coefficient_l1_le x y hy
  have hsum := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun r => |𝔇|)
  simp at hsum
  change (∑ r, |𝔇|) ^ 2 ≤ d * 𝖬₁ at hsum
  nlinarith

𝗇 𝔗 spatialSquaredDistance (U i) $ U j.val
𝗇 𝔅 ∏ j : SpatialScaleIndex i, 𝔗
𝗇 𝔈 spatialCardinalPolynomial U i
𝗇 𝔉 spatialCardinalAffine (U i) $ U j.val
𝗇 𝔊 𝙇
𝗃 𝔙 fun _ _ => ἀ _
theorem spatial_cardinal_polynomial_coefficient_l1_square_le
    (U : 𝔊) (hU : ∀ l r, |𝚚₂| ≤ 2) i :
    𝔚 𝔈 ≤
      𝔏 ^ 𝖪₁ *
        𝔅 := by
  rw [spatial_cardinal_polynomial_scale_product]
  have hs := (sq_le_sq₀ (frameCoefficientL1_nonneg _) $ Finset.prod_nonneg 𝔙 frameCoefficientL1_nonneg ).mpr $ frameCoefficientL1_prod Finset.univ fun j : SpatialScaleIndex i => 𝔉
  calc
    _ ≤ (∏ j : SpatialScaleIndex i, frameCoefficientL1 𝔉) ^ 2 := hs
    _ = ∏ j : SpatialScaleIndex i, 𝔚 𝔉 := by rw [Finset.prod_pow]
    _ ≤ ∏ j : SpatialScaleIndex i, 𝔏 * 𝔗 :=
      Finset.prod_le_prod₀ 𝔙 sq_nonneg
         fun j _ => spatial_cardinal_affine_coefficient_l1_square_le _ _ $ hU j.val
    𝘿 := by rw [Finset.prod_mul_distrib]; simp

𝗇 𝔍 𝙮
def spatialMatrixL1 (A : 𝔍 → 𝔍 → ℝ) : ℝ :=
  ∑ β, ∑ β', |A β β'|

𝗇 𝔐 Finset.sum_nonneg 𝔙 abs_nonneg
theorem spatial_matrix_l1_nonnegative (A : 𝔍 → 𝔍 → ℝ) :
    0 ≤ spatialMatrixL1 A := Finset.sum_nonneg fun _ _ => 𝔐

𝗇 𝔘 𝘒₁
𝗇 𝔄 spatialCardinalScale lam 𝔘 U i
𝗇 𝔎 spatialMatrixL1 $ spatialCenteredCardinalMatrix (D := D) i lam U t
𝗇 𝔖 highFrameCoefficients 𝔈 β
theorem spatial_centered_matrix_l1_eq i lam
    (U : 𝔊) t :
    𝔎 =
      |𝔄| *
        (∑ β : 𝔍, |𝔖|) ^ 2 := by
  unfold spatialMatrixL1 spatialCenteredCardinalMatrix
  simp_rw [abs_mul]
  rw [show ∑ β : 𝔍, ∑ β' : 𝔍,
      |𝔄| *
        |𝔖| *
        |highFrameCoefficients 𝔈 β'| =
      |𝔄| *
        (∑ β : 𝔍, |𝔖|) *
         ∑ β : 𝔍, |𝔖| by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, ← Finset.mul_sum]]
  ring

theorem spatial_cardinal_scale_nonnegative i lam
    (U : 𝔊) t (ht : 𝘩₁) :
    0 ≤ 𝔄 := by
  rw [spatial_cardinal_scale_product]
  exact Finset.prod_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (ht j) $ sq_nonneg _ ) 𝙫

𝗇 𝔓 spatialCardinalWeight lam 𝔘 U i
theorem spatial_cardinal_weight_eq_scale_distance_product i lam
    (U : 𝔊) t :
    𝔓 =
      𝔄 *
        𝔅 ^ 2 := by
  rw [spatial_cardinal_weight_scale_product, spatial_cardinal_scale_product, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  unfold spatialUnaryWeight
  ring

/-- Actual pointwise cardinal matrix envelope. Multiplication by the true
Gamma weight avoids division, so this includes every collision. -/
theorem spatial_centered_matrix_l1_square_le_weight_scale
    i lam (U : 𝔊) (hU : ∀ l r, |𝚚₂| ≤ 2)
    t (ht : 𝘩₁) :
    𝔎 ^ 2 ≤
      𝔓 *
        (𝔏 ^ (2 * 𝖪₁) *
          𝔄) := by
  have hn := spatial_cardinal_scale_nonnegative i lam U t ht
  have hc := (sq_le_sq₀ 𝔐
    $ frameCoefficientL1_nonneg _ ).mpr $ highFrameCoefficients_sum_abs_le (D := D) 𝔈
  rw [spatial_centered_matrix_l1_eq, abs_of_nonneg hn]
  have hprod : 0 ≤ 𝔅 :=
    Finset.prod_nonneg fun j _ => 𝗫₁
  have hs := (sq_le_sq₀ (mul_nonneg hn $ sq_nonneg _ ) $ mul_nonneg hn $ mul_nonneg  𝖠₃  hprod ).mpr
    $ mul_le_mul_of_nonneg_left (hc.trans $ spatial_cardinal_polynomial_coefficient_l1_square_le U hU i ) hn
  apply hs.trans_eq
  rw [spatial_cardinal_weight_eq_scale_distance_product]
  ring
