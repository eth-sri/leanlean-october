module

public import NearlyMinimax.HigherBandRows
public import NearlyMinimax.HighUnionSource
public import NearlyMinimax.FinePairRowAnnihilation
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Original source primitive legality for each actual higher-target
cardinal/cardinal-band row. The selected family supplies positive actual
variation; all law, centering, Borel, and reset facts are derived. -/
𝚸
𝚪
𝚨
𝚩
𝛆
𝚬

𝗇 𝔄 HighPacketMarkIndex 𝙮 m r D q
𝗇 𝔍 𝗥₂*b
𝗇 𝔏 (Z × 𝔄) × Covariate d
𝗃 𝔖 ἀ a b m r D
𝗇 𝔐 𝔖 densityPacketAtom
𝗃 𝔙 densityMargin a b (𝔐 ἀ).1 / 𝔍
theorem highPacketSlope_joint_measurable_general [MeasurableSpace Z]
    (d m r D q : ℕ) (a b : ℝ) (B : Z → Covariate d → 𝗢)
    (hB : 𝗠₂) :
    Measurable fun ex : 𝔏 =>
      𝔖 highPacketSlope q (fun ζ l => B ζ ex.2 l) ex.1 := by
  have hc : Measurable fun ex : 𝔏 =>
      𝔙 ex.1.2.1 :=
    (measurable_of_countable fun h : 𝔄 =>
      𝔙 h.1 ).comp
        $ measurable_snd.comp measurable_fst
  have he (l : Fin r) : Measurable fun ex : 𝔏 =>
      (𝔐 ex.1.2.1).2 l :=
    (measurable_of_countable fun h : 𝔄 =>
      (𝔐 h.1).2 l ).comp $ measurable_snd.comp measurable_fst
  exact hc.mul 𝚜

𝗇 𝔇 C.densityLower+𝗙
𝗇 𝔈 C.densityUpper-𝗙
𝗃 𝔗 ἀ d r
def higherBandSourceRow (C : ModelConstants d) (k r m D q : ℕ)
    (M Cfr lam L T : ℝ) (fine : Bool) :
    𝙭₁ Unit fun _ => 𝔗 HigherBandRowMark m D q fine :=
  higherBandRowData d k r m D q 𝔇 𝔈 Cfr lam L T fine

𝗇 𝔅 densityPacketAtom_mem a b hab.le m r D e.2.1
𝗇 𝔉 B j ζ x l
𝗇 𝔊 fun ζ l => hBb j ζ x l
𝗇 𝔎 𝔗 higherBandCarrierAmplitude_cost_integrable D lam L T hT fine
𝗃 𝔑 𝔗 ἀ m D q a b Cfr lam L T fine
𝗃 𝔒 ἀ σ a b ha hab m r D q hr Cfr A hA hc hpos (fun ζ l => 𝔉) (hBm j x) 𝔊
𝗇 𝔓 𝔗 higherBandCarrierAmplitude_measurable D lam fine
𝗇 𝔔 𝔗 higherBandCarrierMeasure_finite L T hT fine
𝗃 𝔘 ἀ σ a b m r D q Cfr A hA hc hpos
/-- Every actual selected positive-mass higher-band row satisfies the
source's primitive probability, reset, and mean-one balancing inputs. -/
theorem higherBandSourceRow_guards (C : ModelConstants d)
    k r m D q (hr : 𝘗) M Cfr lam L T fine
    (hM : 𝘧) (hCfr : 𝗹) (hT : 𝖹)
    (hpos : 0 < 𝔗 higherBandRowMass m D q 𝔇
      𝔈 Cfr lam L T fine) :
    HighUnionSourceGuards C M Cfr $ higherBandSourceRow C k r m D q M Cfr lam L T fine := by
  let a := 𝔇
  let b := 𝔈
  let σ := 𝔗 higherBandCarrierMeasure L T fine
  let A := 𝔗 higherBandCarrierAmplitude D lam fine
  let B := fun j ζ x l =>
    𝔗 higherBandCarrierFactor lam fine ζ l 𝗂₂
  letI := 𝔔
  have hA := 𝔓
  have hc := 𝔎
  have hg := 𝚀₁ hM
  have hM0 : 𝚌 := 𝖡₄
  have ha : 𝙆 := by linarith [C.densityLower_pos,one_div_pos.mpr hM0]
  have hab : 𝙭 := by
    linarith [highCenterRadius_pos C,(highCenterRadius_le_margins C).1,
      (highCenterRadius_le_margins C).2]
  have hB j (l : Fin r) :=
    (𝔗 higherBandCarrierFactor_joint_measurable lam fine l).comp
      $ measurable_fst.prodMk $ (highLocalCoordinates_measurable d k j).comp measurable_snd
  have hBb j (ζ : 𝔗 HigherBandCarrier fine) (x : Covariate d) (l : Fin r) :=
    𝔗 higherBandCarrierFactor_bound lam fine ζ l _ fun i =>
      (highLocalCoordinates_abs_le_one d k j x i).trans 𝖠₄
  have hBm j (x : Covariate d) (l : Fin r) : Measurable fun ζ => 𝔉 :=
    (hB j l).comp $ measurable_id.prodMk measurable_const
  have hp := 𝔘 highPacketAbsoluteLaw_probability
  refine {
    resolution := hM
    frame := hCfr
    row_probability := fun _ => hp
    mass_nonneg := fun _ => hpos.le
    total_positive := ?_
    activation_measurable := ?_
    activation_bound := fun _ => 𝔑 higherBandRowActivation_bound
    activation_centered := fun _ => 𝔘 highPacketActivation_centered
    slope_measurable := ?_
    slope_integrable := ?_
    slope_centered := ?_
    intercept_measurable := fun _ => 𝔖 highPacketIntercept_measurable q
    intercept_interval := ?_
    row_reset_interval := ?_
    vector_measurable := ?_
    time_measurable := ?_
    vector_ball := ?_
    time_interval := ?_ }
  · simpa [highRowTotalMass,higherBandSourceRow,higherBandRowData] using hpos
  · intro i
    exact absoluteActivation_measurable _ _ $ 𝔖 highPacketMarkWeight_measurable q Cfr A hA
  · intro j i
    exact highPacketSlope_joint_measurable_general d m r D q a b (fun ζ x l => 𝔉) $ hB j
  · intro j x i
    exact 𝔒 highPacketSlope_integrable
  · intro j x i
    exact 𝔒 highPacketAbsoluteLaw_slope_integral_zero
  · intro i e
    exact (𝔅).1
  · intro j i e x v hv
    have hh := localDensityReset_mem_interval a b ha hab r hr
      (𝔐 e.2.1).1 (𝔅).1
      (𝔐 e.2.1).2 (𝔅).2
      (fun _ => v) (fun _ l => B j e.1 x l) () hv $ hBb j e.1 x
    convert hh using 1 <;>
      dsimp [higherBandSourceRow,higherBandRowData,highPacketSlope,highPacketIntercept,localDensityReset] <;> ring
  · intro i γ
    exact (measurable_of_countable fun h : 𝔄 =>
      (highResponseMarkAtom Cfr q h.2).2 γ ).comp measurable_snd
  · intro i
    exact (measurable_of_countable fun h : 𝔄 =>
      (highResponseMarkAtom 0 q h.2).1 ).comp measurable_snd
  · intro i e
    exact covarianceAtom_mem_ball Cfr  𝖡₄  ..
  · intro i e
    exact responseNode_mem_unit q _


/-- The actual higher-band response atoms kill every bounded Borel
observable of the retained carrier and density atom index. -/
theorem higherBandRow_density_observable_zero d r m D q
    a b Cfr lam L T fine (hT : 𝖹)
    (hpos : 0 < 𝔑 higherBandRowMass)
    H
    (hH : Measurable H) B (hB : ∀ z, ‖H z‖ ≤ B) :
     ∫ e, 𝔑 higherBandRowActivation e * H 𝘆₂
      ∂𝔑 higherBandRowLaw = 0 := by
  letI := 𝔔
  exact highPacketAbsoluteLaw_density_observable_zero _ a b m r D q Cfr _
    𝔓
    𝔎
    hpos H hH B hB
