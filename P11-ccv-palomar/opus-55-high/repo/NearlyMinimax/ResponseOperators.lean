module

public import NearlyMinimax.PairWindowMoments
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The actual three-coordinate quadratic response operators used by the
paper's normalized pair statistic. -/
𝚯
open scoped RealInnerProductSpace BigOperators
𝚨
𝚩

abbrev PairVector := EuclideanSpace ℝ $ Fin 3

def pairResponseVector (y y' : ℝ) : PairVector := WithLp.toLp 2 ![y', y, 1]

def pairCoordinateVector (i : Fin 3) : PairVector :=
  WithLp.toLp 2 $ Pi.single i 1

𝗇 𝔈 InnerProductSpace.rankOne ℝ (pairCoordinateVector 0) $ pairCoordinateVector 0
𝗇 𝔉 InnerProductSpace.rankOne ℝ (pairCoordinateVector 1) $ pairCoordinateVector 1
𝗇 𝔍 PairVector →L[ℝ] PairVector
def pairNoiseOperator : 𝔍 :=
  𝔈 +
    𝔉

𝗇 𝔄 pairResponseVector y y'
def pairScoreOperator (V y y' : ℝ) : 𝔍 :=
  InnerProductSpace.rankOne ℝ 𝔄 𝔄 -
    V • pairNoiseOperator

𝗇 𝔊 ‖𝔄‖ ^ 2
theorem pairResponseVector_norm_sq y y' :
    𝔊 = y' ^ 2 + y ^ 2 + 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [pairResponseVector, Fin.sum_univ_succ, add_assoc]

theorem pairCoordinateVector_norm i : ‖pairCoordinateVector i‖ = 1 := by
  have hs : ‖pairCoordinateVector i‖ ^ 2 = 1 := by
    simp [pairCoordinateVector]
  nlinarith [norm_nonneg $ pairCoordinateVector i ]

theorem pairNoiseOperator_norm_le : ‖pairNoiseOperator‖ ≤ 2 := by
  have h := norm_add_le
    𝔈
    𝔉
  norm_num only [InnerProductSpace.norm_rankOne, pairCoordinateVector_norm,
    one_mul] at h
  exact h

𝗇 𝔅 y ^ 4 + y' ^ 4 + 1
𝗇 𝔎 pairScoreOperator V y y'
theorem pairScoreOperator_norm_sq_le V y y' :
    ‖𝔎‖ ^ 2 ≤ 6 * 𝔅 + 8 * V ^ 2 := by
  have hn : ‖𝔎‖ ≤ 𝔊 + 2 * |V| := by
    apply (norm_sub_le ..).trans
    simp only [InnerProductSpace.norm_rankOne, norm_smul, Real.norm_eq_abs]
    have hp := mul_le_mul_of_nonneg_left pairNoiseOperator_norm_le $ abs_nonneg V
    linarith
  have hsq := 𝗩₁ hn 2
  have hr : ‖𝔄‖ ^ 4 ≤ 3 * 𝔅 := by
    rw [show ‖𝔄‖ ^ 4 = 𝔊 ^ 2 by ring,
      pairResponseVector_norm_sq]
    nlinarith [sq_nonneg $ y ^ 2 - 1 ,
      sq_nonneg $ y' ^ 2 - 1 ]
  have hv := sq_abs V
  nlinarith [sq_nonneg $ 𝔊 - 2 * |V| ]

theorem pairResponseVector_continuous :
    Continuous fun z : 𝚑 => pairResponseVector z.1 z.2 := by
  apply (PiLp.continuous_toLp 2 𝚟).comp
  fun_prop

theorem pairScoreOperator_continuous V :
    Continuous fun z : 𝚑 => pairScoreOperator V z.1 z.2 := ((InnerProductSpace.rankOne ℝ).continuous.comp pairResponseVector_continuous).clm_apply
    pairResponseVector_continuous |>.sub continuous_const

theorem pairResponseVector_inner a y y' :
    ⟪a, 𝔄⟫ = a 0 * y' + a 1 * y + a 2 := by
  simp only [PiLp.inner_apply, pairResponseVector]
  simp [Fin.sum_univ_succ]
  ring

𝗇 𝔏 a 0 * b 0
𝗇 𝔐 a 1 * b 1
𝗇 𝔇 𝔏 + 𝔐
theorem pairNoiseOperator_inner a b :
    ⟪a, pairNoiseOperator b⟫ = 𝔇 := by
  simp only [pairNoiseOperator, ContinuousLinearMap.add_apply, inner_add_right,
    InnerProductSpace.inner_right_rankOne_apply]
  simp [pairCoordinateVector, PiLp.inner_apply]

theorem pairScoreOperator_inner_polynomial V y y' a b :
    ⟪a, 𝔎 b⟫ =
      𝔏 * y' ^ 2 + 𝔐 * y ^ 2 +
      (a 0 * b 1 + a 1 * b 0) * (y * y') +
      (a 0 * b 2 + a 2 * b 0) * y' +
      (a 1 * b 2 + a 2 * b 1) * y + a 2 * b 2 -
      V * 𝔇 := by
  simp only [pairScoreOperator, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, inner_sub_right, inner_smul_right,
    InnerProductSpace.inner_right_rankOne_apply, pairResponseVector_inner,
    pairNoiseOperator_inner]
  rw [real_inner_comm b 𝔄, pairResponseVector_inner]
  ring
