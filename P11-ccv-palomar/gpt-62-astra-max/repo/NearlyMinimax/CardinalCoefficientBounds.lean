module

public import NearlyMinimax.HighFrameCoefficientBridge
public import NearlyMinimax.CardinalSeparatedComposition
public import NearlyMinimax.HighFrameNormProduct


@[expose] public section

/-! Actual coefficient bounds for the division-free spatial cardinal
polynomials, including collisions. -/
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {d n : ℕ} (x y : Covariate d) {D : ℕ} (hy : ∀ r, |y r| ≤ 2)
    (A : HighFrameIndex d D → HighFrameVector d D) {i : Fin n} (lam : ℝ) {U : DesignSample d n}
    (hU : ∀ l r, |U l r| ≤ 2)

def spatialAffineExponent (z : Fin d × Bool) : Fin d →₀ ℕ :=
  if z.2 then 0 else Finsupp.single z.1 1

def spatialAffineCoefficient (z : Fin d × Bool) : ℝ :=
  if z.2 then (y z.1 - x z.1) * y z.1 else -8 * (y z.1 - x z.1)

theorem spatial_cardinal_affine_monomial_sum :
    spatialCardinalAffine x y =
      ∑ z, MvPolynomial.monomial (spatialAffineExponent z) (spatialAffineCoefficient x y z) := by
  classical
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Fintype.sum_bool]
  simp only [spatialAffineExponent, spatialAffineCoefficient, Bool.false_eq_true, ite_false, ite_true]
  rw [← MvPolynomial.C_apply, ← MvPolynomial.C_mul_X_eq_monomial, show (-8) * (y r - x r) = -(8 * (y r - x r)) by ring, map_neg]
  ring

include hy in
theorem spatial_cardinal_affine_coefficient_l1_le :
    frameCoefficientL1 (spatialCardinalAffine x y) ≤ 10 * ∑ r, |y r - x r| := by
  rw [spatial_cardinal_affine_monomial_sum]
  apply (frameCoefficientL1_sum_monomial_le _ _).trans
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  rw [Fintype.sum_bool]
  simp [spatialAffineCoefficient]
  norm_num only [abs_neg]
  bound [mul_le_mul_of_nonneg_left (hy r) (abs_nonneg (y r - x r))]

include hy in
/-- The actual affine coefficient norm vanishes at a collision and is
controlled by squared spatial distance everywhere. -/
theorem spatial_cardinal_affine_coefficient_l1_square_le :
    (frameCoefficientL1 (spatialCardinalAffine x y)) ^ 2 ≤ 100 * d * spatialSquaredDistance x y := by
  have hs := (sq_le_sq₀ (frameCoefficientL1_nonneg _) (by positivity)).mpr (spatial_cardinal_affine_coefficient_l1_le x y hy)
  have hsum := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun r => |y r - x r|)
  simp at hsum
  change _ ≤ d * spatialSquaredDistance x y at hsum
  nlinarith

include hU in
theorem spatial_cardinal_polynomial_coefficient_l1_square_le (i : Fin n) :
    (frameCoefficientL1 (spatialCardinalPolynomial U i)) ^ 2 ≤
      (100 * d) ^ Fintype.card (SpatialScaleIndex i) *
        ∏ j : SpatialScaleIndex i, spatialSquaredDistance (U i) (U j.val) := by
  rw [spatial_cardinal_polynomial_scale_product]
  have hp := frameCoefficientL1_prod Finset.univ (fun j : SpatialScaleIndex i => spatialCardinalAffine (U i) (U j.val))
  have hs := (sq_le_sq₀ (frameCoefficientL1_nonneg _) (Finset.prod_nonneg (fun _ _ => frameCoefficientL1_nonneg _))).mpr hp
  calc
    _ ≤ _ := hs
    _ = ∏ j : SpatialScaleIndex i, (frameCoefficientL1 (spatialCardinalAffine (U i) (U j.val))) ^ 2 := by rw [Finset.prod_pow]
    _ ≤ _ :=
      Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _)
        (fun j _ => spatial_cardinal_affine_coefficient_l1_square_le _ _ (hU j.val))
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

def spatialMatrixL1 : ℝ :=
  ∑ β, ∑ β', |A β β'|

theorem spatial_matrix_l1_nonnegative :
    0 ≤ spatialMatrixL1 A := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

theorem spatial_centered_matrix_l1_eq (i : Fin n) (lam : ℝ)
    (U : DesignSample d n) (t : SpatialScaleVector i) :
    let cardinalScale := spatialCardinalScale lam (spatialScaleExtend t) U i
    let coefficients := highFrameCoefficients (spatialCardinalPolynomial U i)
    spatialMatrixL1 (spatialCenteredCardinalMatrix (D := D) lam U t) =
      |cardinalScale| *
        (∑ β : HighFrameIndex d D, |coefficients β|) ^ 2 := by
  intro cardinalScale
  intro coefficients
  unfold spatialMatrixL1 spatialCenteredCardinalMatrix
  simp_rw [abs_mul]
  rw [show (∑ β, ∑ β',
      |cardinalScale| *
        |coefficients β| *
        |coefficients β'|) =
      |cardinalScale| *
        (∑ β, |coefficients β|) *
        (∑ β, |coefficients β|) by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, ← Finset.mul_sum]]
  ring

theorem spatial_cardinal_scale_nonnegative
    (U : DesignSample d n) {t : SpatialScaleVector i} (ht : t ∈ Ici 0) :
    0 ≤ spatialCardinalScale lam (spatialScaleExtend t) U i := by
  rw [spatial_cardinal_scale_product]
  exact Finset.prod_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (ht j) (sq_nonneg _)) (Real.exp_pos _).le)

theorem spatial_cardinal_weight_eq_scale_distance_product (i : Fin n) (lam : ℝ)
    (U : DesignSample d n) (t : SpatialScaleVector i) :
    spatialCardinalWeight lam (spatialScaleExtend t) U i =
      spatialCardinalScale lam (spatialScaleExtend t) U i *
        (∏ j : SpatialScaleIndex i, spatialSquaredDistance (U i) (U j.val)) ^ 2 := by
  rw [spatial_cardinal_weight_scale_product, spatial_cardinal_scale_product, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  grind [spatialUnaryWeight]

include hU in
/-- Actual pointwise cardinal matrix envelope. Multiplication by the true
Gamma weight avoids division, so this includes every collision. -/
theorem spatial_centered_matrix_l1_square_le_weight_scale
    {t : SpatialScaleVector i} (ht : t ∈ Ici 0) :
    (spatialMatrixL1 (spatialCenteredCardinalMatrix (D := D) lam U t)) ^ 2 ≤
      spatialCardinalWeight lam (spatialScaleExtend t) U i *
        ((100 * d) ^ (2 * Fintype.card (SpatialScaleIndex i)) *
          spatialCardinalScale lam (spatialScaleExtend t) U i) := by
  have hn := spatial_cardinal_scale_nonnegative lam U ht
  have hc := (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (frameCoefficientL1_nonneg _)).mpr (highFrameCoefficients_sum_abs_le (D := D) (spatialCardinalPolynomial U i))
  have hb := hc.trans (spatial_cardinal_polynomial_coefficient_l1_square_le hU i)
  rw [spatial_centered_matrix_l1_eq, abs_of_nonneg hn]
  have hprod : 0 ≤ ∏ j : SpatialScaleIndex i, spatialSquaredDistance (U i) (U j.val) :=
    Finset.prod_nonneg (fun j _ => Finset.sum_nonneg (fun r _ => sq_nonneg _))
  have hs := (sq_le_sq₀ (mul_nonneg hn (sq_nonneg _)) (mul_nonneg hn (mul_nonneg (by positivity) hprod))).mpr
    (mul_le_mul_of_nonneg_left hb hn)
  apply hs.trans_eq
  rw [spatial_cardinal_weight_eq_scale_distance_product]
  ring

end NearlyMinimax
