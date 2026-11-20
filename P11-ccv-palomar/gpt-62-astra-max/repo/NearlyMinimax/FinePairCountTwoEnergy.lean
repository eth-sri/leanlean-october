module

public import NearlyMinimax.FinePairScoreBounds
public import NearlyMinimax.CardinalProductDesign


@[expose] public section

/-! Spatial square bounds for the genuine count-two three-row numerator. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

section
variable {d F : ℕ} (hd : 0 < d) {N : ℝ} (hN : 0 ≤ N) (x y : Covariate d) (η : ℝ)

def finePairDistanceFactor (N : ℝ) (x y : Covariate d) : ℝ :=
  (1 + N * exactEuclideanDistance x y) * Real.exp (-(N * exactEuclideanDistance x y))

include hN in
theorem finePairDistanceFactor_nonneg :
    0 ≤ finePairDistanceFactor N x y := by
  exact mul_nonneg (by have h := exactEuclideanDistance_nonneg x y; positivity) (Real.exp_pos _).le

theorem finePairDistanceFactor_measurable (d : ℕ) (N : ℝ) :
    Measurable (fun xy : Covariate d × Covariate d => finePairDistanceFactor N xy.1 xy.2) := by
  exact ((continuous_const.add (exactEuclideanDistance_continuous.const_mul N)).mul
    (exactEuclideanDistance_continuous.const_mul N |>.neg |>.rexp)).measurable

include hN in
theorem finePairDistanceFactor_square_absorption :
    (finePairDistanceFactor N x y)^2 ≤ 6 * Real.exp (-(N * exactEuclideanDistance x y)) := by
  unfold finePairDistanceFactor
  rw [mul_pow, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have he : (2 : ℝ) * -(N * exactEuclideanDistance x y) = -(2 * (N * exactEuclideanDistance x y)) := by ring
  rw [he]
  exact pair_defect_exponential_absorption
    (mul_nonneg hN (exactEuclideanDistance_nonneg x y))

theorem finePairDistanceFactor_square_integrable (hN : 0 < N) :
    let jointLaw := (volume.restrict (spatialPatchBox d)).prod (volume.restrict (spatialPatchBox d))
    Integrable (fun xy : Covariate d × Covariate d => (finePairDistanceFactor N xy.1 xy.2)^2)
      (jointLaw) := by
  intro jointLaw
  have hm := (finePairDistanceFactor_measurable d N).pow_const 2
  have he : Integrable (fun xy : Covariate d × Covariate d =>
      Real.exp (-(N * exactEuclideanDistance xy.1 xy.2)))
      (jointLaw) :=
    Integrable.of_bound
      (exactEuclideanDistance_continuous.const_mul N |>.neg |>.rexp).measurable.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun xy => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr
          (mul_nonneg hN.le (exactEuclideanDistance_nonneg _ _))))
  apply (he.const_mul 6).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun xy => by
    rw [Real.norm_eq_abs, abs_sq]
    exact finePairDistanceFactor_square_absorption hN.le _ _

include hd in
theorem finePairDistanceFactor_square_integral_le (hN : 0 < N) :
    let jointLaw := (volume.restrict (spatialPatchBox d)).prod (volume.restrict (spatialPatchBox d))
    (∫ xy : Covariate d × Covariate d, (finePairDistanceFactor N xy.1 xy.2)^2
      ∂jointLaw) ≤
      6 * (2 : ℝ)^d * spatialExponentialConstant d / N^d := by
  intro jointLaw
  have he : Integrable (fun xy : Covariate d × Covariate d =>
      Real.exp (-(N * exactEuclideanDistance xy.1 xy.2)))
      (jointLaw) :=
    Integrable.of_bound
      (exactEuclideanDistance_continuous.const_mul N |>.neg |>.rexp).measurable.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun xy => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr
          (mul_nonneg hN.le (exactEuclideanDistance_nonneg _ _))))
  have hi := integral_mono (finePairDistanceFactor_square_integrable hN) (he.const_mul 6)
    (fun xy => finePairDistanceFactor_square_absorption hN.le xy.1 xy.2)
  rw [integral_const_mul] at hi
  exact hi.trans ((mul_le_mul_of_nonneg_left (by simpa only [spatialPatchBox_real_volume] using exactEuclideanDistance_pair_exponential_integral_le hd hN (spatialPatchBox d) (by rw [spatialPatchBox_volume]; finiteness))
    (by norm_num : (0 : ℝ) ≤ 6)).trans_eq (by ring))

theorem fine_pair_scalar_product_abs_le {b L d w0 w1 : ℝ} (p0 p1 m0 m1 : ℝ)
    (hb : 0 ≤ b) (hL : 0 ≤ L) (hd : 0 ≤ d)
    (hw0 : |w0| ≤ 1) (hw1 : |w1| ≤ 1) (hp0 : |p0| ≤ b) (hp1 : |p1| ≤ b)
    (hm0 : |m0| ≤ L) (hm1 : |m1| ≤ L) :
    |η^2 * w0 * w1 * p0 * p1 * d * m0 * m1| ≤ η^2 * b^2 * L^2 * d := by
  have hw : |w0*w1| ≤ 1 := by
    rw [abs_mul]
    bound
  have hp : |p0*p1| ≤ b^2 := by
    rw [abs_mul, pow_two]
    bound
  have hm : |m0*m1| ≤ L^2 := by
    rw [abs_mul, pow_two]
    bound
  have hprod := mul_le_mul (mul_le_mul hw hp (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)) hm
    (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 1 * b^2)
  have hs := mul_le_mul_of_nonneg_left hprod (mul_nonneg (sq_nonneg η) hd)
  calc
    _ = _ := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_sq, abs_of_nonneg hd]
      simp
      ring
    _ ≤ _ := hs
    _ = _ := by ring

end

variable {d F : ℕ} [NeZero d] (hF : 3 ≤ F) {ad bd T0 N : ℝ} (haD : 0 < ad) (hab : ad < bd) (hT0 : 0 ≤ T0)
    (hN : T0 ≤ N) {D M q : ℕ} (hD : 2 ≤ D) (hM : 2 ≤ M) (hq : 2 ≤ q) (C a V η ρ : ℝ) (hC : C ≠ 0)
    (ha : 0 < a) (hρ : 0 ≤ ρ) {U : DesignSample d 2} (hU : ∀ i, U i ∈ hyperplaneCube d)
    {p g w : Fin 2 → ℝ} (hp : ∀ i, p i ∈ Icc ad bd) (hw : ∀ i, |w i| ≤ 1) {c : HighFrameVector d F}
    (hf : ∀ i, |coefficientRegression η g w (fun i => highFrameFeature (U i)) c i| ≤ ρ)
include hC hD hF hM hN hT0 hU ha haD hab hf hp hq hw hρ

theorem finePairCountTwoRawNumerator_abs_le
    (y : Fin 2 → Fin 3) :
    |finePairCountTwoRawNumerator ad bd T0 N D M q C a V η U p g w c y| ≤
      (η^2 * bd^2 * ((2*ρ+a)/a^2)^2) * finePairDistanceFactor N (U 0) (U 1) := by
  unfold finePairCountTwoRawNumerator
  rw [finePairThreeRow_count_two_numerator hF haD hab hT0 hN D hD hM hq
    C a V η hC hU hp g w c y]
  exact fine_pair_scalar_product_abs_le η _ _ _ _ (haD.trans hab).le (by positivity)
    (finePairDistanceFactor_nonneg (hT0.trans hN) _ _) (hw 0) (hw 1)
    (by grind)
    (by grind)
    (ternary_mean_derivative_abs_bound ha hρ (hf 0) (y 0))
    (ternary_mean_derivative_abs_bound ha hρ (hf 1) (y 1))

theorem finePairCountTwoRawNumerator_sum_square_le :
    let distanceFactor := finePairDistanceFactor N (U 0) (U 1)
    let numerator := finePairCountTwoRawNumerator ad bd T0 N D M q C a V η U p g w c
    let ratio := η^2 * bd^2 * ((2*ρ+a)/a^2)^2
    (∑ y : Fin 2 → Fin 3,
      (numerator y)^2) ≤
      9 * (ratio)^2 * (distanceFactor)^2 := by
  intro distanceFactor
  intro numerator
  intro ratio
  have hb : 0 ≤ (ratio) * distanceFactor :=
    mul_nonneg (by positivity) (finePairDistanceFactor_nonneg (hT0.trans hN) _ _)
  have hy (y : Fin 2 → Fin 3) :
      (numerator y)^2 ≤
      ((ratio) * distanceFactor)^2 := by
    have h := finePairCountTwoRawNumerator_abs_le hF haD hab hT0 hN hD hM hq
      C a V η ρ hC ha hρ hU hp hw hf y
    simpa using (sq_le_sq₀ (abs_nonneg _) hb).mpr h
  exact (Finset.sum_le_sum (fun y _ => hy y)).trans_eq (by simp; ring)

end NearlyMinimax
