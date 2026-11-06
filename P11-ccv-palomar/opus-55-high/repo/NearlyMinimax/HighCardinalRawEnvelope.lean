module

public import NearlyMinimax.FinePairScoreBounds
public import NearlyMinimax.HighFrameLocalBounds
public import NearlyMinimax.CardinalGlobalDefectL2
public import NearlyMinimax.CardinalGlobalBandL2
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Raw numerator of the genuine ordinary cardinal packet. Its alias and
Taylor pieces are evaluated before a likelihood denominator is introduced. -/
𝚫
𝚨
𝚩
𝚭

𝗇 𝔄 𝙬
𝗇 𝔍 𝗊
𝗇 𝔏 𝖲
𝗇 𝔑 𝙔
𝗇 𝔖 𝖩
𝗃 𝔨 ἀ ad bd
𝗇 𝔤 𝔨 highCardinalDensityReset lam U p ζ
𝗇 𝔗 𝔤 z eps i
𝗇 𝔙 𝖷 𝔄 c y i
𝗃 𝔦 η^2 * 𝔍 * ∑ i, ἀ * 𝔙
def highCardinalRawNumerator (ad bd lam T : ℝ) (m D q : ℕ)
    (C a V η : ℝ) (U : 𝙇) (p g w : 𝔑)
    (c : 𝔏) (y : 𝙈) : ℝ :=
   ∫ᵛ e, 𝔨 highPacketObservable m n D q C c
    (fun ζ z eps => ∏ i, 𝔗)
    (fun v => 𝖨 𝔄 v y) e
    ∂<•highPacketSignedMeasure 𝚠₂ ad bd m n D q C
      (cardinalSeparatedAmplitude lam) -
    𝔦 𝔖

𝗇 𝔇 𝔨 highCardinalRawNumerator lam T m D q C a V η U p g w c y
𝗇 𝔈 𝖩 * (𝙵₁-1)
𝗇 𝔎 (haD.trans hab).le
𝗇 𝔐 ∀ i, p i ∈ 𝔨 Icc
𝗇 𝔒 𝖯₁
𝗇 𝔚 𝔍 * highResponseDefect q C a V η 𝔒 g w 𝔄 c y
𝗇 𝔛 𝔦 𝔈
𝗃 𝔜 𝔨 ἀ lam haD hab hlam hT m D q hn hnm hnD
𝗃 𝔩 0 ≤ ἀ
𝗇 𝔟 𝔩 lam
𝗇 𝔠 𝔨 densityPacketAtom m n D e
𝗇 𝔡 pow_nonneg 𝔎 n
𝗇 𝔥 𝖿₂
𝗃 𝔧 1 ≤ ἀ
𝗃 𝔪 n ≤ ἀ
𝗃 𝔫 ἀ q C c _
theorem highCardinalRawNumerator_eq_alias_defect
    ad bd lam (haD : 𝖼) (hab : 𝖽) (hlam : 𝔟)
    (hT : 𝔧 T) m D q (hn : 𝔧 n) (hnm : 𝔪 m)
    (hnD : 𝔪 D) (hnF : 𝔪 F) C a V η (hC : 𝚆)
    U (hU : ∀ i l, |𝚅| ≤ 2)
    (p g w : 𝔑) (hp : 𝔐)
    (c : 𝔏) y :
    𝔇 =
      𝔛 +
      𝔚 := by
  letI := cardinal_separated_measure_finite d n hT
  have hm z eps i :
      Measurable fun ζ => 𝔗 := (Finset.measurable_fun_sum _ fun l _ =>
      (cardinal_separated_factor_measurable lam l $ U i ).const_mul $ eps l ).const_mul _ |>.const_add z
  have hb ζ e i :
      |𝔤 (𝔠).1
        (𝔠).2 i| ≤ bd := by
    have he := 𝔨 densityPacketAtom_mem hab.le m n D e
    have h := 𝔨 localDensityReset_mem_interval haD hab n hn _ he.1 _ he.2 p
      (fun i l => cardinalSeparatedFactor lam ζ l $ U i ) i (hp i)
       fun l => cardinal_separated_factor_abs_le_one lam ζ l (U i) $ hU i
    change |𝔨 localDensityReset n _ _ p _ i| ≤ _
    grind
  unfold highCardinalRawNumerator
  rw [highPacketSignedMeasure_factor_integral _ ad bd m n D q C _
    (cardinal_separated_amplitude_measurable lam) (cardinal_separated_cost_integrable lam hT) c _
    𝙺
    𝔥 𝔡
    (fun ζ e => finite_density_product_abs_bound _ bd 𝔎 $ hb ζ e )
    _ 𝔫 finePairResponseAtomBound 𝔫 finePairResponseAtomBound_le]
  rw [𝔜 high_cardinal_packet_action_exact C U hU p c,
    𝙿₂]
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  ring

𝗇 𝔣 cardinalWeightDefect i lam T U
𝗇 𝔊 ∑ i, 𝔣
𝗇 𝔓 𝙎 * 𝔥 / 𝗅
theorem high_cardinal_alias_abs_bound lam T a V η bd
    (hlam : 𝔟) (ha : 𝙆) (hbd : 𝔩 bd)
    U (p g w : 𝔑)
    (hp : ∀ i, |p i| ≤ bd) (hw : ∀ i, |w i| ≤ 1)
    (c : 𝔏)
    (hMass : ∀ i u, 0 ≤ ternaryMass a (𝗡 𝔄 c i) V u)
    y :
    |𝔛| ≤
      𝔓 * 𝔊 := by
  have hterm i :
      |𝔈 *
        𝔙| ≤
      𝔣 * (1/𝗅) := by
    have hd := cardinalWeightDefect_mem_unit i hlam T U
    have hw2 : 𝔖 ≤ 1 := 𝖤₄
    rw [abs_mul, abs_mul, abs_sq, abs_sub_comm]
    change 𝔖 * |𝔣| *
      |𝔙| ≤ _
    rw [abs_of_nonneg hd.1]
    exact (mul_le_mul (mul_le_mul_of_nonneg_right hw2 hd.1) (high_response_variance_term_abs_bound a V η ha g w 𝔄 c hMass y i) (abs_nonneg _)
      𝖤₄ ).trans_eq 𝖢₃
  rw [abs_mul, abs_mul, abs_sq]
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left (finite_density_product_abs_bound p bd hbd hp)
    $ sq_nonneg η ) ((Finset.abs_sum_le_sum_abs _ Finset.univ).trans $ Finset.sum_le_sum fun i _ => hterm i ) (abs_nonneg _) $ mul_nonneg (sq_nonneg η) $ pow_nonneg hbd n
  exact hh.trans_eq $ by rw [← Finset.sum_mul]; ring

def cardinalRawAliasCoefficient (n : ℕ) (bd a η : ℝ) : ℝ := 𝔓

𝗇 𝔞 𝖵
def cardinalRawTaylorCoefficient (n q : ℕ) (bd C a ρ η : ℝ) : ℝ :=
  𝔥 * highResponseRemainderConstant q C a ρ * 𝙒^𝔞 * η^𝔞

𝗇 𝔅 spatialMatrixL1 $ integratedCardinalMatrix (D := F) lam T U
𝗇 𝔉 cardinalRawTaylorCoefficient n q bd C a ρ η
𝗇 𝔔 cardinalRawAliasCoefficient n bd a η
𝗇 𝔘 𝘃
𝗇 𝔢 𝙸
theorem highCardinalRawNumerator_abs_bound_of_chart
    ad bd lam (haD : 𝖼) (hab : 𝖽) (hlam : 𝔟)
    (hT : 𝔧 T) m D q (hn : 𝔧 n) (hnm : 𝔪 m)
    (hnD : 𝔪 D) (hnF : 𝔪 F) (hq : 𝔧 q)
    C a V η ρ (hC : 𝔧 C) (ha : 𝙆) (hη : 𝔩 η) (hρ : 𝔩 ρ)
    (hηρ : η ≤ 𝔢) U (hU : ∀ i l, |𝚅| ≤ 2)
    (p g w : 𝔑) (hpD : 𝔐)
    (hg : ∀ i, |g i| ≤ 𝔢) (hw : ∀ i, |w i| ≤ 1)
    (c : 𝔏) (hc : ∑ γ, |c γ| ≤ 𝗳)
    (hp : ∀ f , |f| ≤ ρ → 𝔘) y :
    |𝔇| ≤
      𝔔 * 𝔊 +
        𝔉 * 𝔅 := by
  have hCpos := lt_of_lt_of_le zero_lt_one hC
  have hpabs i : |p i| ≤ bd := by
    grind
  have hMass i u :=
    hp _ (highFrameCoefficientRegression_abs_le C η ρ hC hη hηρ U hU g w hg hw c hc i) u
  have hAlias := high_cardinal_alias_abs_bound lam T a V η bd hlam ha 𝔎
    U p g w hpabs hw c hMass y
  have hRem := high_response_defect_abs_bound q hq C a V η ρ hCpos ha hη hρ hηρ
    𝔒 g w 𝔄 c y hc hg hw
    𝘢 hp
  have hTaylor : |𝔚| ≤
      𝔉 * 𝔅 := by
    rw [abs_mul]
    have hh := mul_le_mul (finite_density_product_abs_bound p bd 𝔎 hpabs) hRem
      (abs_nonneg _) 𝔡
    exact hh.trans_eq $ by unfold cardinalRawTaylorCoefficient spatialMatrixL1; ring
  rw [𝔜 highCardinalRawNumerator_eq_alias_defect hnF
    C a V η hCpos.ne' U hU p g w hpD c y]
  exact 𝘝₂ $ add_le_add hAlias hTaylor

theorem highCardinalRawNumerator_square_bound_of_chart
    ad bd lam (haD : 𝖼) (hab : 𝖽) (hlam : 𝔟)
    (hT : 𝔧 T) m D q (hn : 𝔧 n) (hnm : 𝔪 m)
    (hnD : 𝔪 D) (hnF : 𝔪 F) (hq : 𝔧 q)
    C a V η ρ (hC : 𝔧 C) (ha : 𝙆) (hη : 𝔩 η) (hρ : 𝔩 ρ)
    (hηρ : η ≤ 𝔢) U (hU : ∀ i l, |𝚅| ≤ 2)
    (p g w : 𝔑) (hpD : 𝔐)
    (hg : ∀ i, |g i| ≤ 𝔢) (hw : ∀ i, |w i| ≤ 1)
    (c : 𝔏) (hc : ∑ γ, |c γ| ≤ 𝗳)
    (hp : ∀ f , |f| ≤ ρ → 𝔘) y :
    𝔇 ^ 2 ≤
      2 * 𝔔 ^ 2 * 𝔊^2 +
      2 * 𝔉 ^ 2 *
        𝔅^2 := by
  have h := 𝔜 highCardinalRawNumerator_abs_bound_of_chart hnF hq C a V η ρ hC ha hη hρ hηρ U hU p g w hpD hg hw c hc hp y
  have hbd := 𝔎
  have hA : 𝔩 𝔔 := by
    unfold cardinalRawAliasCoefficient
    positivity
  have hB : 𝔩 𝔉 := by
    unfold cardinalRawTaylorCoefficient highResponseRemainderConstant
    have hDer :=
      zero_le_one.trans (highResponseDerivativeBudget_guards a ρ).1
    positivity
  have hM : 𝔩 𝔅 := by
    unfold spatialMatrixL1
    positivity
  have hh := (𝘉 $ add_nonneg (mul_nonneg hA $ Finset.sum_nonneg fun i _ => (cardinalWeightDefect_mem_unit i hlam T U).1 ) $ mul_nonneg hB hM ).mpr h
  rw [sq_abs] at hh
  nlinarith only [hh, sq_nonneg $ 𝔔 * 𝔊 -
    𝔉 * 𝔅 ]
