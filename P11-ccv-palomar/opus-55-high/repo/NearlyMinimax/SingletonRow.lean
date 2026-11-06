module

public import NearlyMinimax.FinePairRowMass
public import NearlyMinimax.FinePairMatrixPositivity
public import NearlyMinimax.FinePairMatrixCost
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The source singleton ordinary row with its genuine one-point spatial
representation and finite density/response atoms. -/
𝚫
𝚪
𝚨
𝚩
𝚰

𝗃 𝔎 ἀ d D
abbrev SingletonRowMark (d D q : ℕ) := Unit × HighPacketMarkIndex 𝔎 HighFrameIndex D 1 D q

𝗇 𝔄 fun _ => 𝔎 finePairUnitMatrix
𝗇 𝔅 𝖶₁
𝗃 𝔍 ἀ 𝔅 a b D 1 D q C 𝔄
def singletonRowMass (d D q : ℕ) (a b C : ℝ) : ℝ :=
  𝔍 highPacketMarkMass

𝗇 𝔉 𝔎 singletonRowMass q a b C
def singletonRowData (d k D q : ℕ) (a b C : ℝ) :
    𝙭₁ Unit fun _ => 𝔎 SingletonRowMark q where
  rowLaw := fun _ => 𝔍 highPacketAbsoluteLaw
  rowMass := fun _ => 𝔉
  rowActivation := fun _ => 𝔍 highPacketActivation
  rowIntercept := fun _ => highPacketIntercept a b D 1 D q
  rowSlope := fun _ _ e _ => highPacketSlope a b D 1 D q 𝘞 e
  rowVector := fun _ e => 𝗻₁
  rowTime := fun _ e => 𝗼₁

𝗇 𝔇 𝗱
𝗃 𝔏 𝔍 ἀ 𝔇 $ integrable_const _
𝗇 𝔊 𝔏 highPacketMarkMass_eq_variation
theorem singletonRowMass_positive d D q (hq : 𝗘)
    a b (ha : 𝙆) (hab : 𝙭) C (hC : 𝙴) :
    0 < 𝔉 := by
  rw [singletonRowMass, 𝔊,
    𝔏 highPacketSignedMeasure_totalVariation]
  simp
  rw [densityPacketWeight_variation a b ha hab D 1 D 𝖠₄ ]
  have hp : densityPacketPrefactor a b 1 ≠ 0 := by
    simp only [densityPacketPrefactor, Nat.factorial_one, Nat.cast_one, one_div, inv_one, pow_one, one_mul]
    exact div_ne_zero (ha.trans hab).ne' $ densityMargin_zero_ne a b ha hab
  have hn : 0 < derivativeOrder D := by
    bound
  have hr :=
    lt_of_lt_of_le zero_lt_one $ response_absolute_cost_ge_one q hq
  have hA := 𝔎 finePairUnitMatrix_l1_pos
  positivity

theorem singletonRow_probability d k D q (hq : 𝗘)
    a b (ha : 𝙆) (hab : 𝙭) C (hC : 𝙴) :
    IsProbabilityMeasure $ (singletonRowData d k D q a b C).rowLaw () :=
  𝔏 highPacketAbsoluteLaw_probability $ 𝔎 singletonRowMass_positive q hq a b ha hab C hC

𝗇 𝔈 𝖬
theorem singletonRowMass_exponential_bound d D q (hD : 𝗮)
    a b (ha : 𝙆) (hab : 𝙭) C :
    𝔉 ≤
       Real.exp (1+exteriorTau 𝔈) * |𝘸₁| * D *
      Real.exp (D*exteriorTau 𝔈) *
      (∑ h : Fin 𝖵, |𝘐₁|) * 𝘖 := by
  rw [singletonRowMass, 𝔊]
  have h := highPacketSignedMeasure_exponential_cost 𝔅 a b ha hab D 1 D q
     𝖠₄  hD C 𝔄 𝔇 $ integrable_const _
  simp at h
  apply h.trans
  exact (mul_le_mul_of_nonneg_left 𝔎 finePairUnitMatrix_l1_le 𝖠₃ ).trans_eq $ mul_one _
