module

public import NearlyMinimax.FinePairRowSource
public import NearlyMinimax.FinePairRowAnnihilation
public import NearlyMinimax.HighUnionSourceGeometry
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Genuine complete fine-pair union mass-indicator annihilation. The
response coordinates are summed out of the actual signed packets; no
invariant-law or conditional score equality is assumed. -/
𝚸
𝚪
𝚨
𝚩
𝛆
𝚬

𝗇 𝔇 𝙺₂
abbrev FinePairRowDensityMark (d D M : ℕ) : FinePairRowTag → Type
  | .unit => Unit × HighDensityMarkIndex D 2 D
  | .coarse => 𝔇 × HighDensityMarkIndex D 2 D
  | .fine => 𝔇 × FinePairDensityIndex M

𝗃 𝔄 ἀ d D M
𝗇 𝔈 𝔄 FinePairRowDensityMark i
instance (d D M : ℕ) (i : FinePairRowTag) : MeasurableSpace 𝔈 := by
  cases i <;> dsimp only [FinePairRowDensityMark] <;> infer_instance

def finePairRowDensityProj (d D M q : ℕ) (i : FinePairRowTag) :
    𝔄 FinePairRowMark q i → 𝔈 := by
  cases i <;> exact fun e => 𝘆₂

def finePairRowWithResponse (d D M q : ℕ) (i : FinePairRowTag)
    (r : HighResponseMarkIndex 𝙮 q) :
    𝔈 → 𝔄 FinePairRowMark q i := by
  cases i <;> exact fun e => (e.1,(e.2,r))

theorem finePairRowWithResponse_measurable d D M q i
    r :
    Measurable $ 𝔄 finePairRowWithResponse q i r := by
  cases i <;> exact measurable_fst.prodMk $ measurable_snd.prodMk measurable_const

𝗇 𝔉 𝖼₂
𝗃 𝔊 𝔄 ἀ q a b C T₀ N i
theorem finePairRow_density_observable_zero (d : ℕ) [NeZero d] D M q
    a b C T₀ N (hpos : ∀ i, 0 < 𝔊 finePairRowMass)
    i F (hF : Measurable F)
    L (hL : 𝘛₂) :
     ∫ e, 𝔊 finePairRowActivation e *
      F (𝔄 finePairRowDensityProj q i e) ∂𝔊 finePairRowLaw = 0 := by
  cases i
  · exact highPacketAbsoluteLaw_density_observable_zero 𝖶₁ a b D 2 D q C
      𝗻 𝗱 (integrable_const _)
      (hpos .unit) F hF L hL
  · exact highPacketAbsoluteLaw_density_observable_zero (finePairTimeFieldMeasure d 0 T₀)
      a b D 2 D q C _ 𝔉
      (finePairTimeMatrix_cost_integrable d 0 T₀ _) (hpos .coarse) F hF L hL
  · exact finePairPacketAbsoluteLaw_density_observable_zero (finePairTimeFieldMeasure d T₀ N)
      a b M q C _ 𝔉
      (finePairTimeMatrix_cost_integrable d T₀ N _) (hpos .fine) F hF L hL

𝗇 𝔅 𝗋₁
𝗃 𝔍 fun e => ἀ $ Sum.inl e
/-- True complete-union action equals the sum of its actual uncentered
row actions, for any bounded measurable observable. -/
theorem highUnionSource_bounded_action [Fintype I]
    [𝙪] (C : ModelConstants d)
    (R : 𝗽) (G : 𝗗)
    (hpos : 𝚣)
    Fobs (hF : Measurable Fobs)
    L (hL : ∀ e, ‖Fobs e‖ ≤ L) :
     ∫ e, 𝗾 e * Fobs e
      ∂𝗛 =
      ∑ i, ∫ e, R.rowActivation i e * Fobs 𝔅 ∂ R.rowLaw i := by
  letI := G.row_probability
  have hi i : Integrable (R.rowActivation i) $ R.rowLaw i :=
    (integrable_const $ R.rowMass i ).mono' (G.activation_measurable i).aestronglyMeasurable
      $ Filter.Eventually.of_forall fun e => by
        simpa only [Real.norm_eq_abs] using G.activation_bound i e
  have hUi := highRowUnionActivation_integrable R.rowLaw R.rowMass R.rowActivation
    G.activation_measurable hi
  have hUFi := hUi.mul_bdd (hF.comp measurable_inl).aestronglyMeasurable
    $ Filter.Eventually.of_forall 𝔍 hL
  rw [highUnionActivation, highUnionLaw, highCenteredRowUnionActivation,
    highCenteredRowUnionLaw, balancedActivation_integral _ _ 𝘗₁
      (highCenterMix_mem C).2.le _
      (highRowUnionActivation_measurable _ _ G.activation_measurable) Fobs hF hUFi]
  exact highRowUnionActivation_action R.rowLaw R.rowMass hpos G.total_positive
    R.rowActivation G.activation_measurable 𝔍 Fobs
    (hF.comp measurable_inl) fun i => (hi i).mul_bdd
      (hF.comp $ measurable_inl.comp $ rowSigmaMk_measurable i ).aestronglyMeasurable
        $ Filter.Eventually.of_forall fun e => hL 𝔅

section
variable {d k D M q : ℕ} [NeZero k] [NeZero d] [LinearOrder 𝙯]
    (C : ModelConstants d) (Cfr T₀ N : ℝ)
