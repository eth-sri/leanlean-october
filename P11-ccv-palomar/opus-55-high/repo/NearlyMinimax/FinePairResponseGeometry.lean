module

public import NearlyMinimax.HighCardinalScores
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual two-coordinate Hessian extraction of the finite response rule. -/
𝛄
𝚨
𝚩
𝚭

𝗇 𝔞 δ v i
𝗇 𝔎 f i + z * 𝔞
𝗇 𝔄 finiteProductSecond Finset.univ (fun i z => ternaryMass a 𝔎 V $ y i ) (fun i z => 𝔞 * ternaryMeanDerivative a 𝔎 (y i)) (fun i _ => 𝔞 ^ 2 * ternaryMeanSecondDerivative a (y i)) 0
𝗇 𝔐 𝖷 φ c y
𝗇 𝔑 covariance_direction_product C η A hC hA w φ c
𝗇 𝔒 𝗡
𝗇 𝔔 𝙎
𝗇 𝔖 spatialFrameCovariance A φ
𝗇 𝔟 𝔔 * w 0 * w 1
𝗃 𝔠 fun v => highResponseProduct a V η g w ἀ v y
𝗃 𝔢 ternaryMeanDerivative a (𝔒 ἀ c 0) $ y 0
𝗃 𝔣 ternaryMeanDerivative a (𝔒 ἀ c 1) $ y 1
theorem high_response_matrix_two_general [Fintype ι] [DecidableEq ι]
    q (hq : 𝖯₂) C a V η A
    (hC : 𝚆) (hA : ∀ i j, 𝘩 = A j i)
    (g w : 𝖷₂) φ (c : 𝙛) y :
    𝗔 A c 𝔠 φ =
      𝔔 * w 0 ^ 2 * 𝔖 0 0 * 𝔐 0 +
      𝔔 * w 1 ^ 2 * 𝔖 1 1 * 𝔐 1 +
      𝔟 * 𝔖 0 1 *
        𝔢 φ *
        𝔣 φ := by
  let δ := coefficientDirection η w φ c
  let f := 𝔒 φ c
  let m := fun i => ternaryMeanDerivative a (f i) $ y i
  let e := 𝔐
  have he1 : ({0, 1} : Finset $ Fin 2 ).erase 1 = {0} := 𝖨₃
  have hs v : 𝔄 =
       2 * e 0 * (δ v 0 * δ v 0) + 2 * e 1 * (δ v 1 * δ v 1) +
         2 * m 0 * m 1 * (δ v 0 * δ v 1) := by
    simp [finiteProductSecond, Finset.univ_fin2, he1, e, highResponseVarianceTerm,
      ternary_heat_identity]
    ring
  rw [high_response_matrix_second q hq C a V η A g w φ c y]
  change 𝙖 * covarianceAction C A
    (fun v => 𝔄) = _
  simp_rw [hs]
  rw [covarianceAction_add, covarianceAction_add]
  simp_rw [covarianceAction_mul]
  rw [𝔑 0 0,
    𝔑 1 1,
    𝔑 0 1]
  ring

𝗇 𝔉 𝙣
def finePairCoordinatePolynomial (l : Fin d) : 𝔉 := C 8 * X l

𝗃 𝔥 ∑ l, ἀ l ^ 2
def finePairSquarePolynomial (d : ℕ) : 𝔉 :=
  𝔥 finePairCoordinatePolynomial

theorem finePairCoordinatePolynomial_degree (l : Fin d) :
    (finePairCoordinatePolynomial l).totalDegree ≤ 1 := (totalDegree_mul ..).trans 𝖢₄

theorem finePairSquarePolynomial_degree d :
    (finePairSquarePolynomial d).totalDegree ≤ 2 := by
  apply (totalDegree_finsetSum ..).trans
  apply Finset.sup_le
  intro l _
  exact (totalDegree_pow ..).trans $ by nlinarith only [finePairCoordinatePolynomial_degree l]

𝗇 𝔍 fun r => x r / 8
theorem finePairCoordinatePolynomial_eval l (x : Covariate d) :
    eval 𝔍 (finePairCoordinatePolynomial l) = x l := by
  simp only [finePairCoordinatePolynomial, map_mul, eval_C, eval_X]
  ring

theorem finePairSquarePolynomial_eval d (x : Covariate d) :
    eval 𝔍 (finePairSquarePolynomial d) = ∑ r, x r ^ 2 := by
  simp only [finePairSquarePolynomial, map_sum, map_pow, finePairCoordinatePolynomial_eval]

𝗃 𝔓 ἀ d F
𝗇 𝔏 𝔓 HighFrameIndex
𝗇 𝔜 highFrameCoefficients (1 : 𝔉) β
def finePairUnitMatrix (d F : ℕ) (β β' : 𝔏) : ℝ :=
  𝔜 * highFrameCoefficients 1 β'

𝗇 𝔗 highFrameCoefficients $ finePairCoordinatePolynomial l
𝗇 𝔘 highFrameCoefficients $ finePairSquarePolynomial d
def finePairDistanceMatrix (d F : ℕ) (β β' : 𝔏) : ℝ :=
   ∑ l : Fin d, 2 * 𝔗 β *
    𝔗 β' -
    𝔘 β * highFrameCoefficients 1 β' -
    𝔜 *
      𝔘 β'

𝗃 𝔤 𝔓 ἀ β β'
theorem finePairUnitMatrix_symmetric d F β β' :
    𝔤 finePairUnitMatrix = 𝔓 finePairUnitMatrix β' β := mul_comm ..

theorem finePairDistanceMatrix_symmetric d F β β' :
    𝔤 finePairDistanceMatrix = 𝔓 finePairDistanceMatrix β' β := by
  unfold finePairDistanceMatrix
  grind

theorem spatial_frame_covariance_outer [Fintype κ] [DecidableEq κ]
    (u v : 𝖱₁) φ (i j : Fin n) :
    spatialFrameCovariance (fun β β' => u β * v β') φ i j =
      (∑ β, φ i β * u β) * ∑ β, φ j β * v β := by
  simp only [spatialFrameCovariance, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  grind

theorem spatial_frame_covariance_sub [Fintype κ] [DecidableEq κ]
    (A B : κ → 𝖱₁) φ (i j : Fin n) :
    spatialFrameCovariance (fun β β' => A β β' - B β β') φ i j =
      𝔖 i j - spatialFrameCovariance B φ i j := by
  simp only [spatialFrameCovariance, mul_sub, Finset.sum_sub_distrib]

𝗇 𝔇 fun l => highFrameFeature $ U l
𝗇 𝔈 ∑ β : 𝔏, highFrameFeature x β * highFrameCoefficients 1 β = 1
𝗇 𝔙 𝙇
theorem finePairUnitMatrix_kernel (U : 𝔙) i j :
    spatialFrameCovariance 𝔓 finePairUnitMatrix 𝔇 i j = 1 := by
  unfold finePairUnitMatrix
  rw [spatial_frame_covariance_outer]
  have he x : 𝔈 := by
    simpa only [map_one] using (high_frame_polynomial_evaluation 1
       𝖢₄  x).symm
  simp_all

𝗇 𝔚 spatialSquaredDistance (U i) $ U j
𝗃 𝔡 ∑ β : 𝔏, highFrameFeature x β * ἀ β
theorem finePairDistanceMatrix_kernel (hF : 3 ≤ F)
    (U : 𝔙) i j :
    spatialFrameCovariance 𝔓 finePairDistanceMatrix 𝔇 i j =
      -𝔚 := by
  have hc x : 𝔈 := by
    simpa only [map_one] using (high_frame_polynomial_evaluation 1
       𝖢₄  x).symm
  have hl x l : 𝔡 𝔗 = x l := (high_frame_polynomial_evaluation (finePairCoordinatePolynomial l)
      ((finePairCoordinatePolynomial_degree l).trans 𝖡₃ ) x).symm.trans
        $ finePairCoordinatePolynomial_eval l x
  have hs x : 𝔡 𝔘 = 𝔥 x := (high_frame_polynomial_evaluation (finePairSquarePolynomial d)
      ((finePairSquarePolynomial_degree d).trans 𝖡₃ ) x).symm.trans
        $ finePairSquarePolynomial_eval d x
  unfold finePairDistanceMatrix
  rw [spatial_frame_covariance_sub, spatial_frame_covariance_sub,
    spatial_frame_covariance_sum]
  simp_rw [spatial_frame_covariance_rank_one, spatial_frame_covariance_outer, hc, hl, hs]
  simp only [mul_one, one_mul, spatialSquaredDistance, ← Finset.sum_sub_distrib]
  rw [← Finset.sum_neg_distrib]
  grind

def finePairCombinedMatrix (d F : ℕ) (W : ℝ) (β β' : 𝔏) : ℝ :=
  𝔤 finePairUnitMatrix + W * 𝔤 finePairDistanceMatrix

theorem finePairCombinedMatrix_symmetric d F W β β' :
    𝔓 finePairCombinedMatrix W β β' = 𝔓 finePairCombinedMatrix W β' β := by
  simp only [finePairCombinedMatrix, 𝔤 finePairUnitMatrix_symmetric,
    𝔤 finePairDistanceMatrix_symmetric]

theorem spatial_frame_covariance_scalar [Fintype κ] [DecidableEq κ]
    (A : κ → 𝖱₁) (W : ℝ) φ (i j : Fin n) :
    spatialFrameCovariance (fun β β' => W * A β β') φ i j = W * 𝔖 i j := by
  simp only [spatialFrameCovariance, Finset.mul_sum]
  grind

𝗇 𝔊 𝔓 finePairCombinedMatrix W
theorem finePairCombinedMatrix_kernel (hF : 3 ≤ F) W
    (U : 𝔙) i j :
    spatialFrameCovariance 𝔊 𝔇 i j =
      1 - W * 𝔚 := by
  unfold finePairCombinedMatrix
  rw [spatial_frame_covariance_add, spatial_frame_covariance_scalar,
    finePairUnitMatrix_kernel, finePairDistanceMatrix_kernel hF]
  ring

𝗇 𝔅 𝙬
𝗇 𝔛 p 0 * p 1
/-- Exact two-observation remainder after the single diagonal variance
correction, with the paper's concrete fixed coefficient matrices. -/
theorem finePairResponseCountTwo_numerator (hF : 3 ≤ F)
    q (hq : 𝖯₂) C a V η W (hC : 𝚆)
    (U : 𝖿₁) (p g w : 𝖷₂)
    c y :
    𝔛 * 𝗔 𝔊 c
      𝔠 𝔅 -
      𝔔 * 𝔛 * ∑ i, 𝖩 *
        𝖷 𝔅 c y i =
      𝔟 * p 0 * p 1 *
        (1 - W * 𝘘₂) *
        𝔢 𝔅 *
        𝔣 𝔅 := by
  rw [high_response_matrix_two_general q hq C a V η 𝔊 hC
    $ 𝔓 finePairCombinedMatrix_symmetric W , Fin.sum_univ_two]
  simp only [finePairCombinedMatrix_kernel hF, spatialSquaredDistance, sub_self,
    zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero]
  ring
