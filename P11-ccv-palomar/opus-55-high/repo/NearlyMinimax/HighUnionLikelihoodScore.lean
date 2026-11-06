module

public import NearlyMinimax.HighUnionFieldScore
public import NearlyMinimax.HighUnionSourceGeometry
public import NearlyMinimax.HighUnionSourceModel
public import NearlyMinimax.HighHistoryLikelihoodScore
public import NearlyMinimax.HighWindowLikelihoodAlgebra
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Exact global likelihood-score decomposition for the actual complete
marked source. The squared window partition counts the variance correction once. -/
𝚯
𝚪
𝚨
𝛆
𝚩
𝚬

𝗇 𝔔 Function.update c j u
𝗃 𝔜 ἀ d k
𝗇 𝔗 𝔜 highLocalFieldWithout D η
theorem highLocalFieldWithout_update (d k D : ℕ) [NeZero k] η
    c
    j u x :
    𝔗 𝔔 j x =
      𝔗 c j x := by
  apply congrArg fun v => η*v
  apply Finset.sum_congr rfl
  simp_all

𝗇 𝔈 fun i => 𝔜 highPeriodicTensor j $ x i
𝗇 𝔉 fun i => highLocalFrameFeature k j $ x i
𝗇 𝔘 𝙇
𝗇 𝔙 𝗑
𝗇 𝔚 𝔜 highFrameField_coefficientRegression D n hk η
𝗃 𝔞 fun i => 𝔗 ἀ j $ x i
theorem highFrameField_update_coefficientRegression (d k D n : ℕ) [NeZero k] (hk : 𝔙)
    η c
    j u
    (x : 𝔘) :
    coefficientRegression η 𝔞 c
      𝔈
      𝔉 u =
      fun i => 𝔜 highFrameField η (fun l => highFramePolynomial $ 𝔔 l ) $ x i := by
  simpa only [Function.update_self, highLocalFieldWithout_update] using 𝔚 𝔔 j x

section ActualSource
𝗇 𝔛 𝔜 HighWindowLabels
variable {d k D : ℕ} {I : Type*} [Fintype I] {E : 𝗀}
  [𝙪] [NeZero k] [LinearOrder 𝔛]
  (C : ModelConstants d) (R : 𝔜 HighUnionRowData D I E)

𝗇 𝔄 fun i j => j ∈ 𝔜 highNeighborLabels i
𝗇 𝔅 fun {_ _} h => 𝔜 highNeighborLabels_symmetric _ _ h
𝗇 𝔇 𝖯
𝗇 𝔎 𝖷₁
𝗇 𝔐 highUnionResponseReset R e $ 𝔇 j
𝗇 𝔑 historyMarkedAppend 𝔄 𝔅 j 𝔎
theorem highUnionSourceState_append_coefficients j
    h
    e :
    (highUnionSourceState C R 𝔑).2 =
      Function.update 𝔇 j
        𝔐 := by
  rw [highUnionSourceState_append R C j h e]
  rfl

𝗇 𝔏 𝔞 𝔇
𝗇 𝔖 highUnionSourceRegression C R η
theorem highUnionSourceRegression_append (n : ℕ) (hk : 𝔙) (η : ℝ)
    (j : 𝔛)
    h
    (e : HighUnionMark E) (x : 𝔘) :
    coefficientRegression η
      𝔏
      𝔈
      𝔉
      𝔐 =
      fun i => 𝔖
        𝔑 $ x i := by
  unfold highUnionSourceRegression
  rw [highUnionSourceState_append_coefficients C R j h e]
  exact 𝔜 highFrameField_update_coefficientRegression D n hk η _ j _ x

𝗇 𝔊 𝗛
𝗇 𝔍 𝗾
𝗇 𝔒 HistoryMarked 𝔄 $ HighUnionMark E
𝗇 𝔓 highUnionSourceDensity C R
/-- The true local score, evaluated on the actual canonical history and
its actual appended reset states. -/
def highUnionSourceLocalScore (n : ℕ) (a V η : ℝ)
    (h : 𝔒)
    (x : 𝔘) (j : 𝔛) (y : 𝙈) : ℝ :=
  𝔜 highFrameMarkedScore D n
    (fun _ => 𝔊)
    (fun _ => 𝔍) a V η
    (fun i => 𝔓 h $ x i )
    (fun l e i => 𝔓
      (historyMarkedAppend 𝔄
        𝔅 l 𝔎) $ x i )
    (fun l e => highUnionResponseReset R e $ 𝔇 l )
    𝔇 x j y

theorem highUnionSourceAppendLikelihoodAction_eq_responseAction n (hk : 𝔙)
    a V η j
    (h : 𝔒)
    x y :
    highAppendLikelihoodAction 𝔄
      𝔅
      𝔊 𝔍
      n a V 𝔓 𝔖 j h 𝖮 =
    highMarkedResponseAction 𝔊
      𝔍 a V η
      (fun e i => 𝔓
        𝔑 $ x i )
      (fun e => 𝔐)
      𝔏
      𝔈
      𝔉 y := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun e => by
    dsimp
    unfold highRawSampleLikelihood
    rw [Finset.prod_mul_distrib]
    unfold highResponseProduct
    rw [highUnionSourceRegression_append C R n hk η j h e x]
    ring

/-- The global append/heat likelihood score is exactly the sum of the
true local window scores. This uses the actual reset recursion and exact
squared partition, with no statistical energy premise. -/
theorem highUnionSourceLikelihoodScore_eq_sum n (hk : 𝔙) a V η
    (h : 𝔒)
    x y :
    highHistoryLikelihoodScore 𝔄
      𝔅
      𝔊 𝔍
      n a V η 𝔓 𝔖 h 𝖮 =
      ∑ j, highUnionSourceLocalScore C R n a V η h x j y := by
  simp only [highUnionSourceLocalScore, highFrameMarkedScore]
  rw [highMarkedLocalScore_sum_of_partition
    (hreg := fun j => 𝔚
      𝔇 j x)
    (hpartition := fun i => 𝔜 highPeriodicTensor_sq_partition  𝖡₃  $ x i )]
  unfold highHistoryLikelihoodScore highHistoryLikelihoodDerivative
  simp_rw [highUnionSourceAppendLikelihoodAction_eq_responseAction C R n hk a V η]
  unfold highRawSampleLikelihood highRawSampleVarianceDerivative highUnionSourceRegression
  rw [Finset.prod_mul_distrib]
  grind
