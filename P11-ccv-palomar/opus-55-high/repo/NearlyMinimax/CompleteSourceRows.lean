module

public import NearlyMinimax.SourceRows
public import NearlyMinimax.FinePairRowSource
public import NearlyMinimax.HigherBandRowSource
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! All primitive source guards for the complete singleton, pair, and
higher coarse/fine row family. Numerical guards are the only inputs. -/
𝚸
𝚪
𝚨
𝚩
𝛆
𝚬

𝗇 𝔄 C.densityLower+𝗙
𝗇 𝔇 C.densityUpper-𝗙
𝗇 𝔏 𝘧
theorem high_source_interval_numeric (C : ModelConstants d) M
    (hM : 𝔏) :
    0 < 𝔄 ∧ 𝔄 < 𝔇 := by
  have hg := 𝚀₁ hM
  have hM0 : 𝚌 := 𝖡₄
  constructor
  · linarith [C.densityLower_pos,one_div_pos.mpr hM0]
  · linarith [highCenterRadius_pos C,(highCenterRadius_le_margins C).1,
      (highCenterRadius_le_margins C).2]

𝗇 𝔐 1/𝖧
𝗃 𝔒 ἀ d k D
def completeSourceRows (C : ModelConstants d) (k D M q : ℕ)
    (Cfr lam ℓ N μ : ℝ) :=
  𝔒 sourceRowData M q (C.densityLower+𝔐)
    (C.densityUpper-𝔐) Cfr lam ℓ N μ

𝗇 𝔅 𝖶₁
𝗇 𝔈 densityPacketAtom_mem a b hab.le D 1 D e.2.1
𝗃 𝔘 fun _ => ἀ
𝗇 𝔉 𝔘 𝙃
𝗇 𝔊 HighUnionSourceGuards C M Cfr
𝗇 𝔎 𝔘 measurable_const
𝗃 𝔓 ἀ a b D 1 D
𝗇 𝔑 𝔓 densityPacketAtom e.2.1
𝗃 𝔔 ἀ 𝔅 a b D 1 D q Cfr A
𝗃 𝔖 ἀ 𝔅 a b ha hab D 1 D q
/-- The actual singleton response/density row satisfies every source
primitive guard; its nondegeneracy and centering follow from finite rules. -/
theorem singletonRowSource_guards C (k D M q : ℕ)
    (hq : 𝗘) (hM : 𝔏)
    Cfr (hCfr : 𝗹) :
    𝔊
      $ 𝔒 singletonRowData q 𝔄 𝔇 Cfr := by
  let a := 𝔄
  let b := 𝔇
  obtain ⟨ha,hab⟩ := 𝗌₁
  have hCf : 0 < Cfr := 𝖡₄
  have hpos := 𝘇₂ Cfr hCf
  let A := fun _ : Unit => finePairUnitMatrix d D
  have hA : 𝙚 := 𝗱
  have hc : Integrable (separatedMatrixCost A) 𝔅 := by
    simp
  refine {
    resolution := hM
    frame := hCfr
    row_probability := fun _ => 𝔒 singletonRow_probability q hq a b ha hab Cfr hCf
    mass_nonneg := 𝔘 hpos.le
    total_positive := ?_
    activation_measurable := fun _ => absoluteActivation_measurable _ _
      $ 𝔓 highPacketMarkWeight_measurable q Cfr A hA
    activation_bound := fun _ => 𝔔 highPacketActivation_bound
    activation_centered := fun _ => 𝔔 highPacketActivation_centered hA hc hpos
    slope_measurable := ?_
    slope_integrable := ?_
    slope_centered := ?_
    intercept_measurable := fun _ => 𝔓 highPacketIntercept_measurable q
    intercept_interval := fun _ e => (𝔈).1
    row_reset_interval := ?_
    vector_measurable := ?_
    time_measurable := ?_
    vector_ball := fun _ _ => covarianceAtom_mem_ball Cfr hCf ..
    time_interval := fun _ _ => responseNode_mem_unit q _ }
  · simpa [highRowTotalMass,singletonRowData,a,b] using hpos
  · fun_prop
  · intro j x i
    exact 𝔖 highPacketSlope_integrable  𝖠₄  Cfr A hA hc hpos
      𝔉 𝔎 𝖢₄
  · intro j x i
    exact 𝔖 highPacketAbsoluteLaw_slope_integral_zero  𝖠₄ 
      Cfr A hA hc hpos 𝔉 𝔎 𝖢₄
  · intro j i e x v hv
    have hh := localDensityReset_mem_interval a b ha hab 1  𝖠₄ 
      (𝔑).1 (𝔈).1
      (𝔑).2 (𝔈).2
      𝔘 v 𝘞 () hv 𝖢₄
    convert hh using 1 <;> dsimp [singletonRowData,highPacketSlope,highPacketIntercept,localDensityReset] <;> ring
  all_goals fun_prop

𝗃 𝔍 fun _ => ἀ i
𝗃 𝔙 fun j x _ => ἀ j x i
/-- Restricting primitive guards to one genuine positive row preserves
all of them. The one-row total is its actual variation mass. -/
theorem HighUnionSourceGuards.restrict {d k F : ℕ} {I : Type*} [Fintype I] {E : 𝗀}
    [𝙪] {C } {M Cfr }
    {R : 𝗽} (G : 𝔊 R)
    i (hpos : 0 < R.rowMass i) :
    𝔊 $ highUnionRowRestrict R i where
  resolution := G.resolution
  frame := G.frame
  row_probability := 𝔍 G.row_probability
  mass_nonneg := 𝔍 G.mass_nonneg
  total_positive := by simpa [highRowTotalMass,highUnionRowRestrict] using hpos
  activation_measurable := 𝔍 G.activation_measurable
  activation_bound := 𝔍 G.activation_bound
  activation_centered := 𝔍 G.activation_centered
  slope_measurable := fun j _ => G.slope_measurable j i
  slope_integrable := 𝔙 G.slope_integrable
  slope_centered := 𝔙 G.slope_centered
  intercept_measurable := 𝔍 G.intercept_measurable
  intercept_interval := 𝔍 G.intercept_interval
  row_reset_interval := fun j _ => G.row_reset_interval j i
  vector_measurable := 𝔍 G.vector_measurable
  time_measurable := 𝔍 G.time_measurable
  vector_ball := 𝔍 G.vector_ball
  time_interval := 𝔍 G.time_interval

𝗃 𝔗 ἀ C k D M q
/-- The complete actual source family satisfies every primitive source
condition from numerical guards alone. In particular the final prior is
not restricted to the pair rows or a single higher-target packet. -/
theorem completeSourceRows_guards {d : ℕ} (C : ModelConstants d) [NeZero d]
    (k D M q : ℕ) (hD : 𝗕) (hq : 𝗘)
    (hM : 𝔏)
    Cfr lam ℓ N μ (hCfr : 𝗹) (hℓ : 𝙲₁) (hℓN : 𝖰₂) :
    𝔊 $ 𝔗 completeSourceRows Cfr lam ℓ N μ := by
  let a := 𝔄
  let b := 𝔇
  obtain ⟨ha,hab⟩ := 𝗌₁
  have hCf : 0 < Cfr := 𝖡₄
  have hcomp i :
      𝔊 $ 𝔒 sourceRowComponent M q a b Cfr lam ℓ N μ i := by
    cases i with
    | inl p =>
      exact (𝔗 finePairSourceRows_guards hD hq hM Cfr hCfr ℓ N hℓ hℓN).restrict p
        $ 𝙿₁ Cfr hCf ℓ N hℓ hℓN p
    | inr i =>
      cases i with
      | inl _ => exact 𝔗 singletonRowSource_guards hq hM Cfr hCfr
      | inr i =>
        exact higherBandSourceRow_guards C k (higherBandFamilyTarget i.val)
          𝚁 D q
          (by have hh := (higherBandFamily_target_bounds d D M q a b Cfr lam ℓ N μ i).1; omega)
          M Cfr lam ℓ 𝙽 i.val.2 hM hCfr
          i.property.1 i.property.2.2.2
  exact {
    resolution := hM
    frame := hCfr
    row_probability := fun i => (hcomp i).row_probability ()
    mass_nonneg := fun i => (hcomp i).mass_nonneg ()
    total_positive := 𝔒 sourceRowTotalMass_positive M q hq a b ha hab Cfr hCf lam ℓ N μ
    activation_measurable := fun i => (hcomp i).activation_measurable ()
    activation_bound := fun i => (hcomp i).activation_bound ()
    activation_centered := fun i => (hcomp i).activation_centered ()
    slope_measurable := fun j i => (hcomp i).slope_measurable j ()
    slope_integrable := fun j x i => (hcomp i).slope_integrable j x ()
    slope_centered := fun j x i => (hcomp i).slope_centered j x ()
    intercept_measurable := fun i => (hcomp i).intercept_measurable ()
    intercept_interval := fun i => (hcomp i).intercept_interval ()
    row_reset_interval := fun j i => (hcomp i).row_reset_interval j ()
    vector_measurable := fun i => (hcomp i).vector_measurable ()
    time_measurable := fun i => (hcomp i).time_measurable ()
    vector_ball := fun i => (hcomp i).vector_ball ()
    time_interval := fun i => (hcomp i).time_interval () }
