module

public import NearlyMinimax.FinePairRowNondegenerate
public import NearlyMinimax.HighUnionSource
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Concrete source guards for all three actual fine-pair rows. No row-law,
mean-zero, positive variation or reset legality premise is assumed. -/
𝚸
𝚪
𝚨
𝚩
𝚱
𝚬

𝗃 𝔄 ἀ d D M q
𝗇 𝔇 1/𝖧
def finePairSourceRows (C : ModelConstants d) (k D M q : ℕ)
    (Cfr T₀ N : ℝ) :
    𝙭₁ FinePairRowTag 𝔄 FinePairRowMark :=
  finePairRowData d k D M q (C.densityLower+𝔇)
    (C.densityUpper-𝔇) Cfr T₀ N

𝗃 𝔅 ἀ d k D M q a b
𝗃 𝔈 𝔄 ἀ a b Cfr T₀ N
/-- The three true unit/coarse/fine packet rows satisfy every primitive
source guard under their physical numerical parameter conditions. -/
theorem finePairSourceRows_guards (C : ModelConstants d) [NeZero d]
    (k D M q : ℕ) (hD : 𝗕) (hq : 𝗘)
    (hM : 𝘧)
    Cfr (hCfr : 𝗹) T₀ N (hT₀ : 0 < T₀) (hTN : T₀ < N) :
    HighUnionSourceGuards C M Cfr $ finePairSourceRows C k D M q Cfr T₀ N := by
  let a := C.densityLower+𝗙
  let b := C.densityUpper-𝗙
  have hg := 𝚀₁ hM
  have hM0 : 𝙋 < M := 𝖡₄
  have hr := highCenterRadius_pos C
  have hmargin := highCenterRadius_le_margins C
  have ha : 𝙆 := by linarith [C.densityLower_pos, one_div_pos.mpr hM0]
  have hab : 𝙭 := 𝖡₄
  have hCf : 0 < Cfr := 𝖡₄
  have hpos := 𝙿₁ Cfr hCf T₀ N hT₀ hTN
  refine {
    resolution := hM
    frame := hCfr
    row_probability := ?_
    mass_nonneg := ?_
    total_positive := ?_
    activation_measurable := ?_
    activation_bound := ?_
    activation_centered := ?_
    slope_measurable := ?_
    slope_integrable := ?_
    slope_centered := ?_
    intercept_measurable := ?_
    intercept_interval := ?_
    row_reset_interval := ?_
    vector_measurable := ?_
    time_measurable := ?_
    vector_ball := ?_
    time_interval := ?_ }
  · exact 𝔈 finePairRowLaw_probability hpos
  · exact 𝔈 finePairRowMass_nonneg
  · exact Finset.sum_pos' (fun i _ => (hpos i).le) ⟨.unit, Finset.mem_univ _, hpos .unit⟩
  · exact 𝔈 finePairRowActivation_measurable hpos
  · exact 𝔈 finePairRowActivation_bound
  · exact 𝔈 finePairRowActivation_centered hpos
  · exact 𝔅 finePairRowSlope_joint_measurable
  · exact 𝔅 finePairRowSlope_integrable Cfr T₀ N hpos ha hab
  · exact 𝔅 finePairRowSlope_centered Cfr T₀ N hpos ha hab
  · exact 𝔄 finePairRowIntercept_measurable a b
  · exact 𝔄 finePairRowIntercept_mem a b hab.le
  · exact 𝔅 finePairRow_reset_interval ha hab
  · exact 𝔄 finePairRowVector_measurable Cfr
  · exact 𝔄 finePairRowTime_measurable
  · exact 𝔄 finePairRowVector_ball Cfr hCf
  · exact 𝔄 finePairRowTime_unit
