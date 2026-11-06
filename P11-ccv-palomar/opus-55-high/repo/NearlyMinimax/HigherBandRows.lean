module

public import NearlyMinimax.CardinalFactorJoint
public import NearlyMinimax.HighUnionReset
public import NearlyMinimax.HighLocalFrame
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual ordinary target-r rows from the positive separated cardinal
and cardinal-band measures, with their real finite density/response atoms. -/
𝚫
𝚪
𝚨
𝚩
𝚱

𝗃 𝔏 ἀ d r
def HigherBandCarrier (d r : ℕ) : Bool → Type
  | false => 𝔏 CardinalSeparatedMark
  | true => 𝔏 CardinalBandMark

𝗇 𝔈 𝔏 HigherBandCarrier fine
instance higherBandCarrier_measurable (d r : ℕ) (fine : Bool) :
    MeasurableSpace 𝔈 := by
  cases fine <;> dsimp [HigherBandCarrier] <;> infer_instance

instance higherBandCarrier_standardBorel (d r : ℕ) (fine : Bool) :
    StandardBorelSpace 𝔈 := by
  cases fine
  · exact 𝔏 cardinal_separated_mark_standardBorel
  · exact 𝔏 cardinal_band_mark_standardBorel

def higherBandCarrierMeasure (d r : ℕ) (L T : ℝ) :
    (fine : Bool) → Measure 𝔈
  | false => 𝔏 cardinalSeparatedMeasure T
  | true => 𝔏 cardinalBandMeasure L T

𝗇 𝔐 𝙮
def higherBandCarrierAmplitude (d r D : ℕ) (lam : ℝ) :
    (fine : Bool) → 𝔈 → 𝔐 → 𝔐 → ℝ
  | false => cardinalSeparatedAmplitude lam
  | true => cardinalBandAmplitude lam

def higherBandCarrierFactor (d r : ℕ) (lam : ℝ) :
    (fine : Bool) → 𝔈 → Fin r → 𝙀
  | false => cardinalSeparatedFactor lam
  | true => cardinalBandFactor lam

𝗇 𝔄 𝔏 higherBandCarrierMeasure L T fine
theorem higherBandCarrierMeasure_finite d r L T (hT : 𝖹) fine :
    IsFiniteMeasure 𝔄 := by
  cases fine
  · exact 𝔏 cardinal_separated_measure_finite hT
  · exact 𝔏 cardinal_band_measure_finite L hT

𝗇 𝔇 𝔏 higherBandCarrierAmplitude D lam fine
theorem higherBandCarrierAmplitude_measurable d r D lam fine
    i j : Measurable fun ζ => 𝔇 ζ i j := by
  cases fine
  · exact cardinal_separated_amplitude_measurable lam i j
  · exact cardinal_band_amplitude_measurable lam i j

theorem higherBandCarrierAmplitude_cost_integrable d r D lam L T (hT : 𝖹)
    fine : Integrable (separatedMatrixCost 𝔇)
      𝔄 := by
  cases fine
  · exact cardinal_separated_cost_integrable lam hT
  · exact cardinal_band_cost_integrable lam L hT

𝗇 𝔑 𝔏 higherBandCarrierFactor lam fine
theorem higherBandCarrierFactor_joint_measurable d r lam fine l :
    Measurable fun ζx : 𝔈 × Covariate d =>
      𝔑 ζx.1 l ζx.2 := by
  cases fine
  · exact cardinal_separated_factor_joint_measurable lam l
  · exact cardinal_band_factor_joint_measurable lam l

theorem higherBandCarrierFactor_bound d r lam fine
    ζ l x (hx : ∀ i, |x i| ≤ 2) :
    |𝔑 ζ l x| ≤ 1 := by
  cases fine
  · exact cardinal_separated_factor_abs_le_one lam ζ l x hx
  · exact cardinal_band_factor_abs_le_one lam ζ l x hx

abbrev HigherBandRowMark (d r m D q : ℕ) (fine : Bool) :=
  𝔈 × HighPacketMarkIndex 𝔐 m r D q

𝗇 𝔉 𝔏 HigherBandRowMark m D q fine
𝗃 𝔎 ἀ 𝔄 a b m r D q C 𝔇
def higherBandSignedRow (d r m D q : ℕ) (a b C lam L T : ℝ) (fine : Bool) :
    SignedMeasure 𝔉 :=
  𝔎 highPacketSignedMeasure

def higherBandRowMass (d r m D q : ℕ) (a b C lam L T : ℝ) (fine : Bool) : ℝ :=
  𝔎 highPacketMarkMass

def higherBandRowLaw (d r m D q : ℕ) (a b C lam L T : ℝ) (fine : Bool) :
    Measure 𝔉 :=
  𝔎 highPacketAbsoluteLaw

def higherBandRowActivation (d r m D q : ℕ) (a b C lam L T : ℝ) (fine : Bool) :
    𝔉 → ℝ :=
  𝔎 highPacketActivation

𝗃 𝔍 ἀ d r m D q a b C lam L T fine
𝗇 𝔅 𝔍 higherBandRowMass
𝗇 𝔊 𝔍 higherBandRowActivation
def higherBandRowData (d k r m D q : ℕ) (a b C lam L T : ℝ) (fine : Bool) :
    𝙭₁ Unit fun _ => 𝔉 where
  rowLaw := fun _ => 𝔍 higherBandRowLaw
  rowMass := fun _ => 𝔅
  rowActivation := fun _ => 𝔊
  rowIntercept := fun _ => highPacketIntercept a b m r D q
  rowSlope := fun j _ e x => highPacketSlope a b m r D q
    (fun ζ l => 𝔑 ζ l 𝗂₂) e
  rowVector := fun _ e => 𝗻₁
  rowTime := fun _ e => 𝗼₁

theorem higherBandRowMass_eq_variation d r m D q a b C lam L T
    (hT : 𝖹) fine : 𝔅 =
      ((𝔍 higherBandSignedRow).variation univ).toReal := by
  letI := 𝔏 higherBandCarrierMeasure_finite L T hT fine
  exact highPacketMarkMass_eq_variation _ a b m r D q C _
    (𝔏 higherBandCarrierAmplitude_measurable D lam fine)
    $ 𝔏 higherBandCarrierAmplitude_cost_integrable D lam L T hT fine

theorem higherBandRowMass_nonneg d r m D q a b C lam L T fine :
    0 ≤ 𝔅 := signedMarkMass_nonneg ..

theorem higherBandRowActivation_bound d r m D q a b C lam L T fine
    e :
    |𝔊 e| ≤ 𝔅 :=
  absoluteActivation_bound ..
