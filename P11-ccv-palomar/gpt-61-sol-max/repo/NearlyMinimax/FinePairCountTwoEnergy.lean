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

def finePairDistanceFactor {d } N (x y : Covariate d)  :=
  (1 + N * exactEuclideanDistance x y) * Real.exp (-(N * exactEuclideanDistance x y))

theorem finePairDistanceFactor_nonneg {d } {N } (hN : 0 ≤ N) (x y : Covariate d) :
    0 ≤ finePairDistanceFactor N x y := mul_nonneg (by have h := exactEuclideanDistance_nonneg x y; positivity) (Real.exp_pos _).le

theorem finePairDistanceFactor_measurable d N :
    Measurable (fun xy : Covariate d × Covariate d => finePairDistanceFactor N xy.1 xy.2) := ((continuous_const.add (exactEuclideanDistance_continuous.const_mul N)).mul
    (exactEuclideanDistance_continuous.const_mul N |>.neg |>.rexp)).measurable

section
variable {d : ℕ}

theorem finePairDistanceFactor_square_absorption  {N } (hN : 0 ≤ N)
    (x y : Covariate d) :
    (finePairDistanceFactor N x y)^2 ≤ 6 * Real.exp (-(N * exactEuclideanDistance x y)) := by
  unfold finePairDistanceFactor
  rw [mul_pow, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have he : (2 : ℝ) * -(N * exactEuclideanDistance x y) = -(2 * (N * exactEuclideanDistance x y)) := by ring
  rw [he]
  solve_by_elim [pair_defect_exponential_absorption, mul_nonneg, exactEuclideanDistance_nonneg]

theorem finePairDistanceFactor_square_integrable  {N } (hN : 0 < N) :
    Integrable (fun xy  => (finePairDistanceFactor N xy.1 xy.2)^2)
      ((volume.restrict (spatialPatchBox d)).prod (volume.restrict (spatialPatchBox d))) := by
  have hm := (finePairDistanceFactor_measurable d N).pow_const 2
  have he : Integrable (fun xy : Covariate d × Covariate d =>
      Real.exp (-(N * exactEuclideanDistance xy.1 xy.2)))
      ((volume.restrict (spatialPatchBox d)).prod (volume.restrict (spatialPatchBox d))) :=
    Integrable.of_bound
      (exactEuclideanDistance_continuous.const_mul N |>.neg |>.rexp).measurable.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun xy => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        solve_by_elim [Real.exp_le_one_iff.mpr, neg_nonpos.mpr, mul_nonneg, hN.le, exactEuclideanDistance_nonneg])
  apply (he.const_mul 6).mono' hm.aestronglyMeasurable
  simp_all [finePairDistanceFactor_square_absorption, hN.le]

theorem finePairDistanceFactor_square_integral_le  (hd : 0 < d) {N } (hN : 0 < N) :
    (∫ xy : Covariate d × Covariate d, (finePairDistanceFactor N xy.1 xy.2)^2
      ∂(volume.restrict (spatialPatchBox d)).prod (volume.restrict (spatialPatchBox d))) ≤
      6 * 2^d * spatialExponentialConstant d / N^d := by
  have he : Integrable (fun xy : Covariate d × Covariate d =>
      Real.exp (-(N * exactEuclideanDistance xy.1 xy.2)))
      ((volume.restrict (spatialPatchBox d)).prod (volume.restrict (spatialPatchBox d))) :=
    Integrable.of_bound
      (exactEuclideanDistance_continuous.const_mul N |>.neg |>.rexp).measurable.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun xy => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        solve_by_elim [Real.exp_le_one_iff.mpr, neg_nonpos.mpr, mul_nonneg, hN.le, exactEuclideanDistance_nonneg])
  have hi := integral_mono (finePairDistanceFactor_square_integrable hN) (he.const_mul 6)
    (fun xy => finePairDistanceFactor_square_absorption hN.le xy.1 xy.2)
  rw [integral_const_mul] at hi
  exact hi.trans ((mul_le_mul_of_nonneg_left (spatialPatchBox_pair_exponential_integral_le hd hN)
    (by norm_num : (0 : ℝ) ≤ 6)).trans_eq (by ring))
end


def finePairCountTwoRawNumerator {d F } [NeZero d]
    ad bd T0 N D M q C a V η
    U (p g w : Fin 2 → ℝ)
    (c : HighFrameIndex d F → ℝ) y  :=
  finePairThreeRowFirstAction ad bd T0 N D M q C U p c
    (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) -
    η^2 * (p 0 * p 1) * ∑ i, (w i)^2 *
      highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i

theorem fine_pair_scalar_product_abs_le (η b L d w0 w1 p0 p1 m0 m1 : ℝ)
    (hb : 0 ≤ b) (hL : 0 ≤ L) (hd : 0 ≤ d)
    (hw0 : |w0| ≤ 1) (hw1 : |w1| ≤ 1) (hp0 : |p0| ≤ b) (hp1 : |p1| ≤ b)
    (hm0 : |m0| ≤ L) (hm1 : |m1| ≤ L) :
    |η^2 * w0 * w1 * p0 * p1 * d * m0 * m1| ≤ η^2 * b^2 * L^2 * d := by
  have hw : |w0*w1| ≤ 1 := by
    rw [abs_mul]
    bound
  have hp : |p0*p1| ≤ b^2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hp0 hp1 (abs_nonneg _) hb
  have hm : |m0*m1| ≤ L^2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hm0 hm1 (abs_nonneg _) hL
  have hprod := mul_le_mul (mul_le_mul hw hp (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)) hm
    (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 1 * b^2)
  have hs := mul_le_mul_of_nonneg_left hprod (mul_nonneg (sq_nonneg η) hd)
  calc
    _ = (η^2*d) * ((|w0*w1| * |p0*p1|) * |m0*m1|) := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_sq, abs_of_nonneg hd]
      simp only [abs_mul]
      ring
    _ ≤ (η^2*d) * ((1*b^2)*L^2) := hs
    _ = _ := by ring

section
variable {d F : ℕ} [NeZero d] (hF : 3 ≤ F) (ad bd T0 N : ℝ) (haD : 0 < ad) (hab : ad < bd) (hT0 : 0 ≤ T0) (hN : T0 ≤ N) (D M q : ℕ) (hD : 2 ≤ D) (hM : 2 ≤ M) (hq : 2 ≤ q) (C a V η ρ : ℝ) (hC : C ≠ 0) (ha : 0 < a) (hρ : 0 ≤ ρ) (U : Fin 2 → Covariate d) (hU : ∀ i, U i ∈ hyperplaneCube d) (p g w : Fin 2 → ℝ) (hp : ∀ i, p i ∈ Icc ad bd) (hw : ∀ i, |w i| ≤ 1) (c : HighFrameIndex d F → ℝ) (hf : ∀ i, |coefficientRegression η g w (fun i => highFrameFeature (U i)) c i| ≤ ρ)
include hF haD hab hT0 hN hD hM hq hC ha hρ hU hp hw hf

theorem finePairCountTwoRawNumerator_abs_le 
    y :
    |finePairCountTwoRawNumerator ad bd T0 N D M q C a V η U p g w c y| ≤
      (η^2 * bd^2 * ((2*ρ+a)/a^2)^2) * finePairDistanceFactor N (U 0) (U 1) := by
  unfold finePairCountTwoRawNumerator
  rw [finePairThreeRow_count_two_numerator hF ad bd T0 N haD hab hT0 hN D M q hD hM hq
    C a V η hC U hU p hp g w c y]
  exact fine_pair_scalar_product_abs_le η bd ((2*ρ+a)/a^2) (finePairDistanceFactor N (U 0) (U 1))
    _ _ _ _ _ _ (haD.trans hab).le (by positivity)
    (finePairDistanceFactor_nonneg (hT0.trans hN) _ _) (hw 0) (hw 1)
    (by grind)
    (by grind)
    (ternary_mean_derivative_abs_bound a _ ρ ha hρ (hf 0) (y 0))
    (ternary_mean_derivative_abs_bound a _ ρ ha hρ (hf 1) (y 1))

theorem finePairCountTwoRawNumerator_sum_square_le  :
    (∑ y : Fin 2 → Fin 3,
      (finePairCountTwoRawNumerator ad bd T0 N D M q C a V η U p g w c y)^2) ≤
      9 * (η^2 * bd^2 * ((2*ρ+a)/a^2)^2)^2 * (finePairDistanceFactor N (U 0) (U 1))^2 := by
  have hb : 0 ≤ (η^2 * bd^2 * ((2*ρ+a)/a^2)^2) * finePairDistanceFactor N (U 0) (U 1) :=
    mul_nonneg (by positivity) (finePairDistanceFactor_nonneg (hT0.trans hN) _ _)
  have hy (y : Fin 2 → Fin 3) :
      (finePairCountTwoRawNumerator ad bd T0 N D M q C a V η U p g w c y)^2 ≤
      ((η^2 * bd^2 * ((2*ρ+a)/a^2)^2) * finePairDistanceFactor N (U 0) (U 1))^2 := by
    have h := finePairCountTwoRawNumerator_abs_le hF ad bd T0 N haD hab hT0 hN D M q hD hM hq
      C a V η ρ hC ha hρ U hU p g w hp hw c hf y
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb).mpr h
  exact (Finset.sum_le_sum (fun y _ => hy y)).trans_eq (by simp; ring)
end


end NearlyMinimax
