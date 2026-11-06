module

public import NearlyMinimax.FinePairRows
public import NearlyMinimax.FinePairTimeCost
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Nondegeneracy and exact activity costs of the actual fine-pair rows. -/
𝚫
𝚪
𝚨
𝚩
𝚾

𝗇 𝔄 Fin 𝖵
𝗇 𝔉 responseNode q j ^ 2
𝗇 𝔑 responseWeight q j
theorem response_absolute_cost_ge_one q (hq : 𝗘) :
     1 ≤ ∑ j : 𝔄, |𝔑| := by
  calc
    1 = |∑ j : 𝔄, 𝔑 * 𝔉| := by
      rw [response_second_moment q hq]; norm_num
    _ ≤ ∑ j : 𝔄, |𝔑 * 𝔉| :=
      Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ j : 𝔄, |𝔑| := by
      apply Finset.sum_le_sum
      intro j _
      have he : |𝔉| = 𝔉 := 𝗤
      rw [abs_mul, he]
      apply mul_le_of_le_one_right $ abs_nonneg _
      have hj := responseNode_mem_unit q j
      nlinarith [hj.1, hj.2]

𝗃 𝔔 ἀ a b
𝗇 𝔊 𝔔 densityPacketWeight D 2 D h
𝗇 𝔒 HighDensityMarkIndex D 2 D
𝗇 𝔓 𝔔 densityMargin_zero_ne ha hab
theorem ordinary_density_absolute_cost_pos a b (ha : 𝙆) (hab : 𝙭)
    D :
    0 < ∑ h : 𝔒, |𝔊| := by
  rw [𝔔 densityPacketWeight_variation ha hab D 2 D 𝖠₄ ]
  have hb := (ha.trans hab).ne'
  have hθ := 𝔓
  have hp : 𝔔 densityPacketPrefactor 2 ≠ 0 := by
    change 2^2 / 2 * (b / 𝔔 densityMargin 0)^2 ≠ 0
    positivity
  have hn : 0 < derivativeOrder D := by
    bound
  positivity

theorem fine_density_absolute_cost_pos a b (ha : 𝙆) (hab : 𝙭) M :
    0 < ∑ h : FinePairDensityIndex M, |𝔔 finePairDensityWeight M h| := by
  rw [𝔔 finePairDensityWeight_variation ha hab M]
  have hp : 𝔔 finePairDensityPrefactor ≠ 0 :=
    div_ne_zero (pow_ne_zero _ (ha.trans hab).ne') $ pow_ne_zero _ 𝔓
  positivity

𝗇 𝔅 finePairRowMass d D M q a b C T₀ N
𝗇 𝔇 𝘖
𝗇 𝔍 𝗻
𝗃 𝔎 ἀ (Measure.dirac ()) a b D 2 D q C 𝔍 (fun _ _ => measurable_const) $ integrable_const _
theorem finePairRowMass_unit d D M q a b C T₀ N :
    𝔅 .unit =
      (∑ h : 𝔒, |𝔊|) *
      (∑ h : 𝔄, |𝘐₁|) * 𝔇 *
       ∑ i, ∑ j, |finePairUnitMatrix d D i j| := by
  rw [finePairRowMass, 𝔎 highPacketMarkMass_eq_variation,
    𝔎 highPacketSignedMeasure_totalVariation]
  aesop

𝗇 𝔈 𝖼₂
𝗃 𝔏 ἀ _ _ _ _ _ _ _ _ _ 𝔈 $ finePairTimeMatrix_cost_integrable d 0 T₀ _
theorem finePairRowMass_coarse (d : ℕ) [NeZero d] D M q a b C T₀ N
    (hT : 0 ≤ T₀) :
    𝔅 .coarse =
      (∑ h : 𝔒, |𝔊|) *
      (∑ h : 𝔄, |𝘐₁|) * 𝔇 *
      ((∑ i, ∑ j, |𝗀₂ i j|) * (T₀^2/2)) := by
  rw [finePairRowMass, 𝔏 highPacketMarkMass_eq_variation,
    𝔏 highPacketSignedMeasure_totalVariation,
    finePairTimeMatrix_cost_integral d 0 T₀ le_rfl hT]
  simp

𝗃 𝔐 ἀ _ a b M q C _ 𝔈 $ finePairTimeMatrix_cost_integrable d T₀ N _
theorem finePairRowMass_fine (d : ℕ) [NeZero d] D M q a b C T₀ N
    (hT : 0 ≤ T₀) (hTN : T₀ ≤ N) :
    𝔅 .fine =
      (∑ h : FinePairDensityIndex M, |𝔔 finePairDensityWeight M h|) *
      (∑ h : 𝔄, |𝘐₁|) * 𝔇 *
      ((∑ i, ∑ j, |𝗀₂ i j|) * ((𝘚₂-T₀^2)/2)) := by
  rw [finePairRowMass, finePairPacketMarkMass]
  rw [signedMarkMass_eq_variation _ _ 𝔐 finePairPacketWeight_integrable]
  change ((finePairPacketSignedMeasure _ a b M q C _).variation univ).toReal = _
  rw [𝔐 finePairPacketSignedMeasure_totalVariation,
    finePairTimeMatrix_cost_integral d T₀ N hT hTN]
