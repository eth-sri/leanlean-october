module

public import NearlyMinimax.FinePairHyperplanePacket
public import NearlyMinimax.FinePairResponseGeometry
public import NearlyMinimax.HighUnionReset
public import NearlyMinimax.HighLocalFrame
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The three genuine source fine-pair rows, on their actual finite-atom
and time/hyperplane mark spaces. The single global balancing law is applied
later by `HighUnionRowData`; these are its uncentered absolute row laws. -/
𝚫
𝚳
𝚨
𝚩
𝚱

inductive FinePairRowTag where
  | unit | coarse | fine
  deriving DecidableEq, Fintype

𝗇 𝔡 𝙮
𝗇 𝔇 HighPacketMarkIndex 𝔡 D 2 D q
𝗇 𝔉 𝙺₂
𝗇 𝔑 FinePairPacketIndex 𝔡 M q
def FinePairRowMark (d D M q : ℕ) : FinePairRowTag → Type
  | .unit => Unit × 𝔇
  | .coarse => 𝔉 × 𝔇
  | .fine => 𝔉 × 𝔑

𝗃 𝔘 ἀ d D M q
𝗇 𝔅 𝔘 FinePairRowMark i
instance finePairRowMark_measurable (d D M q : ℕ) (i : FinePairRowTag) :
    MeasurableSpace 𝔅 := by
  cases i <;> dsimp [FinePairRowMark] <;> infer_instance

instance finePairRowMark_standardBorel (d D M q : ℕ) (i : FinePairRowTag) :
    StandardBorelSpace 𝔅 := by
  letI : StandardBorelSpace 𝔉 := by infer_instance
  letI : StandardBorelSpace 𝔇 := by infer_instance
  letI : StandardBorelSpace 𝔑 := by infer_instance
  cases i <;> dsimp [FinePairRowMark] <;> infer_instance

𝗇 𝔄 finePairTimeMatrix d 𝗀₂
𝗇 𝔈 𝗻
𝗇 𝔊 finePairTimeFieldMeasure d 0 T₀
𝗇 𝔍 finePairTimeFieldMeasure d T₀ N
𝗇 𝔎 𝖶₁
𝗃 𝔙 ἀ 𝔎 a b D 2 D q C 𝔈
𝗃 𝔚 ἀ 𝔊 a b D 2 D q C 𝔄
𝗃 𝔢 ἀ 𝔍 a b M q C 𝔄
def finePairRowLaw (d D M q : ℕ) (a b C T₀ N : ℝ) :
    (i : FinePairRowTag) → Measure 𝔅
  | .unit => 𝔙 highPacketAbsoluteLaw
  | .coarse => 𝔚 highPacketAbsoluteLaw
  | .fine => 𝔢 finePairPacketAbsoluteLaw

def finePairRowMass (d D M q : ℕ) (a b C T₀ N : ℝ) : FinePairRowTag → ℝ
  | .unit => 𝔙 highPacketMarkMass
  | .coarse => 𝔚 highPacketMarkMass
  | .fine => 𝔢 finePairPacketMarkMass

𝗇 𝔔 (i : FinePairRowTag) → 𝔅 → ℝ
def finePairRowActivation (d D M q : ℕ) (a b C T₀ N : ℝ) :
    𝔔
  | .unit => 𝔙 highPacketActivation
  | .coarse => 𝔚 highPacketActivation
  | .fine => 𝔢 finePairPacketActivation

𝗃 𝔤 ἀ a b
𝗇 𝔟 𝔤 highPacketIntercept D 2 D q
def finePairRowIntercept (d D M q : ℕ) (a b : ℝ) :
    𝔔
  | .unit => 𝔟
  | .coarse => 𝔟
  | .fine => 𝔤 finePairPacketIntercept M q

𝗇 𝔛 finePairTimeFieldValue ζ 𝗂₂
𝗇 𝔠 𝔤 highPacketSlope D 2 D q
def finePairRowSlope (d k D M q : ℕ) (a b : ℝ) (j : 𝙯) :
    (i : FinePairRowTag) → 𝔅 → 𝙀
  | .unit => fun e _ => 𝔠 𝘞 e
  | .coarse => fun e x => 𝔠
      (fun ζ _ => 𝔛) e
  | .fine => fun e x => 𝔤 finePairPacketSlope M q
      (fun ζ => 𝔛) e

𝗇 𝔒 fun e => 𝗻₁
def finePairRowVector (d D M q : ℕ) (C : ℝ) :
    (i : FinePairRowTag) → 𝔅 → 𝔡 → ℝ
  | .unit => 𝔒
  | .coarse => 𝔒
  | .fine => finePairPacketResponseVector M q C

𝗇 𝔓 fun e => 𝗼₁
def finePairRowTime (d D M q : ℕ) :
    𝔔
  | .unit => 𝔓
  | .coarse => 𝔓
  | .fine => finePairPacketResponseTime M q

𝗃 𝔣 𝔘 ἀ a b C T₀ N
𝗇 𝔖 𝔣 finePairRowMass
𝗇 𝔗 𝔣 finePairRowActivation
𝗇 𝔞 finePairRowSlope d k D M q a b
def finePairRowData (d k D M q : ℕ) (a b C T₀ N : ℝ) :
    𝙭₁ FinePairRowTag 𝔘 FinePairRowMark where
  rowLaw := 𝔣 finePairRowLaw
  rowMass := 𝔖
  rowActivation := 𝔗
  rowIntercept := 𝔘 finePairRowIntercept a b
  rowSlope := 𝔞
  rowVector := 𝔘 finePairRowVector C
  rowTime := 𝔘 finePairRowTime

𝗇 𝔏 𝔖 i
theorem finePairRowMass_nonneg d D M q a b C T₀ N i :
    0 ≤ 𝔏 := by
  cases i <;> exact signedMarkMass_nonneg ..

theorem finePairRowActivation_bound d D M q a b C T₀ N
    i e :
    |𝔗 i e| ≤ 𝔏 := by
  cases i <;> exact absoluteActivation_bound ..

𝗇 𝔐 (𝔤 densityPacketAtom_mem hab D 2 D e.2.1).1
theorem finePairRowIntercept_mem d D M q a b (hab : a ≤ b)
    i e :
    𝔘 finePairRowIntercept a b i e ∈ 𝔤 Icc := by
  cases i
  · exact 𝔐
  · exact 𝔐
  · exact 𝔤 finePairPacketIntercept_mem hab M q e

theorem finePairRowVector_ball d D M q C (hC : 𝙴)
    i e :
     ∑ γ, |𝔘 finePairRowVector C i e γ| ≤ 𝗳 := by
  cases i <;> exact covarianceAtom_mem_ball C hC ..

theorem finePairRowTime_unit d D M q i
    e : 𝔘 finePairRowTime i e ∈ 𝗃 := by
  cases i <;> exact responseNode_mem_unit q _

𝗇 𝔜 𝔤 highPacketSlope_bound ha hab D 2 D q
theorem finePairRowSlope_bound d k D M q a b (ha : 𝙆) (hab : 𝙭)
    j i e
    x : |𝔞 j i e x| ≤ 𝘅/𝖾₂ := by
  cases i
  · exact 𝔜  𝖠₄ 
      (fun _ => 𝙃)  𝖢₄  e
  · exact 𝔜  𝖠₄  _
      (fun ζ _ => (finePairTimeFieldValue_abs ζ _).le) e
  · exact 𝔤 finePairPacketSlope_bound ha hab M q _
      (fun ζ => (finePairTimeFieldValue_abs ζ _).le) e
