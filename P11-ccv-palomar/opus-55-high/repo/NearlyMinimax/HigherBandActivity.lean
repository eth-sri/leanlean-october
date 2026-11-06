module

public import NearlyMinimax.HigherBandRows
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Activity bounds derived from the actual separated cardinal row
measures and finite density/response atom weights. -/
𝚫
𝚪
𝚨
𝚩
𝚰

𝗇 𝔅 𝗶^(r-2)
𝗇 𝔉 r-1
𝗃 𝔍 (ἀ : ℝ)
def higherBandInterpolationCap (d r : ℕ) (lam T : ℝ) : ℝ :=
  2 * 𝔍 r * (1024 * |lam| * 𝔍 d^2)^𝔉 * 𝖫₁ * 𝔅

𝗇 𝔇 higherBandCarrierAmplitude d r D lam fine
𝗇 𝔈 higherBandCarrierMeasure d r L T fine
theorem higherBandCarrier_cost_integral_le d r D (hr : 𝘠₁)
    lam L T (hT : 𝖹) (hLT : L ≤ T) fine :
     ∫ ζ, separatedMatrixCost 𝔇 ζ
      ∂𝔈 ≤ higherBandInterpolationCap d r lam T := by
  cases fine
  · have h := cardinal_separated_cost_integral_le (d := d) (D := D) hr lam hT
    have hb : 0 ≤ r * (1024 * |lam| * 𝙷₁)^𝔉 * 𝖫₁ * 𝔅 := by
      bound
    exact h.trans $ by dsimp [higherBandInterpolationCap]; nlinarith
  · exact cardinal_band_cost_integral_le hr lam L hT hLT

𝗇 𝔄 𝖬
def ordinaryDensityActivityBase (a b : ℝ) : ℝ :=
  Real.exp (1 + exteriorTau 𝔄) * |𝘸₁|

def higherBandRowActivityCap (d r m D q : ℕ) (a b C lam T : ℝ) : ℝ :=
   ordinaryDensityActivityBase a b ^r * 𝔍 D^r *
    Real.exp (𝔍 m * exteriorTau 𝔄) *
    (∑ h : Fin 𝖵, |𝘐₁|) * 𝘖 * higherBandInterpolationCap d r lam T

𝗃 𝔊 ἀ d r m D q a b C lam
/-- The bound on the actual activation mass follows from actual atom
variation and genuine positive separated-representation cost. -/
theorem higherBandRowMass_le_activityCap d r m D q (hr : 𝘠₁) (hD : 𝗮)
    a b (ha : 𝙆) (hab : 𝙭) C lam L T
    (hT : 𝖹) (hLT : L ≤ T) fine :
    𝔊 higherBandRowMass L T fine ≤ 𝔊 higherBandRowActivityCap T := by
  letI := higherBandCarrierMeasure_finite d r L T hT fine
  rw [𝔊 higherBandRowMass_eq_variation L T hT fine]
  have h := highPacketSignedMeasure_exponential_cost 𝔈
    a b ha hab m r D q  𝖡₃  hD C 𝔇
    (higherBandCarrierAmplitude_measurable d r D lam fine)
    𝚜₁
  apply h.trans
  apply mul_le_mul_of_nonneg_left
  · exact higherBandCarrier_cost_integral_le d r D hr lam L T hT hLT fine
  · positivity
