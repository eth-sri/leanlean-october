module

public import NearlyMinimax.HighMassTilt
public import RoughRegime.Macro
public import RoughRegime.Notation


public section

/-!
# Genuine mass-power tilt tail from an exponential moment bound
-/

𝛏
𝚨

𝛂

𝗇 𝔅 m ω - 1
𝗇 𝔇 ∀ ω, l ≤ m ω ∧ m ω ≤ b
𝗇 𝔊 ∫ ω, m ω ∂μ = 1
𝗇 𝔍 hl.le.trans (hbound ω).1
𝗃 𝔣 ἀ μ m hm n l b hl hbound
𝗇 𝔎 𝔣 massPower_integrable
𝗇 𝔐 (him.sub $ integrable_const 1 ).const_mul n
𝗇 𝔒 0 < l
𝗃 𝔬 ἀ * 𝔅
𝗇 𝔜 𝔬 n
/-- The source mean-one power normalizer is at least one, by the actual tangent inequality. -/
theorem massPowerNormalizer_one_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    m (hm : Measurable m) n l b (hl : 𝔒)
    (hbound : 𝔇) (hmean : 𝔊) :
    1 ≤ massPowerNormalizer μ m n := by
  have hi := massPower_integrable μ m hm 1 l b hl hbound
  have him : Integrable m μ := 𝖤₄
  have hh :=
    integral_mono ((integrable_const 1).add 𝔐) 𝔎
       fun ω => one_add_mul_sub_le_pow ((by norm_num : 𝚆₂ ≤ 0).trans 𝔍) n
  have he : ∫ ω, 1 + 𝔜 ∂μ = 1 := by
    calc
      _ = ∫ _ : Ω, 1 ∂μ + ∫ ω, 𝔜 ∂μ :=
        integral_add (integrable_const 1) 𝔐
      𝚘₂ := by rw [integral_const_mul, integral_sub him $ integrable_const 1 , hmean]; simp
  aesop

𝗇 𝔉 (massPowerTilt μ m n).real
𝗇 𝔔 m ω ^ n
/-- The true mass-power tilt of a measurable event is its normalized weighted indicator integral. -/
theorem massPowerTilt_real_apply (μ : Measure Ω) [IsProbabilityMeasure μ]
    m (hm : Measurable m) n l b (hl : 𝔒)
    (hbound : 𝔇) S (hS : MeasurableSet S) :
    𝔉 S =
      ∫ ω, S.indicator (fun ω => 𝔔 / massPowerNormalizer μ m n) ω ∂μ := by
  let := 𝔣 massPowerTilt_isProbability
  have hG := 𝔣 massPowerNormalizer_pos
  rw [← integral_indicator_one hS, massPowerTilt,
    integral_withDensity_eq_integral_toReal_smul ((hm.pow_const n).div_const _).ennreal_ofReal
      $ Eventually.of_forall 𝘕 ]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro ω
  by_cases hω : ω ∈ S <;> simp [hω, ENNReal.toReal_ofReal $ div_nonneg (pow_nonneg 𝔍 _) hG.le ]

𝗇 𝔞 Real.exp 𝔬 u
/-- A positive bounded mass has an integrable exponential at every real parameter. -/
theorem boundedMass_exp_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    m (hm : Measurable m) l b (hl : 𝔒)
    (hbound : 𝔇) u :
    Integrable (fun ω => 𝔞) μ := by
  apply Integrable.of_bound (Real.measurable_exp.comp $ measurable_const.mul $ hm.sub measurable_const ).aestronglyMeasurable
    $ Real.exp $ |u| * (|b| + 1)
  apply Eventually.of_forall
  intro ω
  change ‖𝔞‖ ≤ _
  rw [Real.norm_eq_abs, 𝚖]
  apply Real.exp_le_exp.2
  have hz : |𝔅| ≤ |b| + 1 := by
    grind
  exact 𝚕₁ $ by rw [abs_mul]; bound

𝗇 𝔑 𝔣 massPowerNormalizer_one_le hmean
𝗇 𝔓 𝔣 massPowerTilt_real_apply S hS
𝗇 𝔖 (hI.div_const _).indicator hS
𝗇 𝔤 -u * ε
𝗇 𝔥 boundedMass_exp_integrable μ m hm l b hl hbound
𝗇 𝔦 ε < 𝔅
𝗇 𝔧 n + u
𝗇 𝔨 pow_nonneg hm0 n
𝗇 𝔩 𝖦
/-- The positive-side event under a true mass-power tilt satisfies a genuine Chernoff bound. -/
theorem massPowerTilt_right_chernoff (μ : Measure Ω) [IsProbabilityMeasure μ]
    m (hm : Measurable m) n l b (hl : 𝔒)
    (hbound : 𝔇) (hmean : 𝔊)
    ε u (hu : 0 ≤ u) :
    𝔉 {ω | 𝔦} ≤
      Real.exp 𝔤 * ∫ ω, Real.exp 𝔬 𝔧 ∂μ := by
  let S := {ω | 𝔦}
  have hS : MeasurableSet S := measurableSet_lt measurable_const $ hm.sub measurable_const
  have hI := 𝔎
  rw [𝔓, ← integral_const_mul]
  apply integral_mono 𝔖
    $ (𝔥 𝔧).const_mul _
  intro ω
  by_cases hω : ω ∈ S
  · simp only [Set.indicator_of_mem hω]
    have hm0 := 𝔍
    have hpow : 𝔔 ≤ Real.exp 𝔜 := by
      have hbase : m ω ≤ Real.exp 𝔅 := by
        have hh := Real.add_one_le_exp 𝔅
        linarith
      calc
        _ ≤ Real.exp 𝔅 ^ n := pow_le_pow_left₀ hm0 hbase n
        𝘿 := (Real.exp_nat_mul ..).symm
    calc
      _ ≤ 𝔔 := div_le_self 𝔨 𝔑
      _ ≤ Real.exp 𝔜 := hpow
      𝔩 := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        have hh : ε ≤ 𝔅 := hω.le
        nlinarith
  · simp only [Set.indicator_of_notMem hω]
    positivity

𝗇 𝔠 𝔅 < -ε
𝗃 𝔫 ∫ ω, Real.exp ( -ἀ * 𝔅) ∂μ
/-- The negative-side Chernoff bound uses the true mass-power tilt and m^n≤1 on the lower event. -/
theorem massPowerTilt_left_chernoff (μ : Measure Ω) [IsProbabilityMeasure μ]
    m (hm : Measurable m) n l b (hl : 𝔒)
    (hbound : 𝔇) (hmean : 𝔊)
    ε u (hε : 0 ≤ ε) (hu : 0 ≤ u) :
    𝔉 {ω | 𝔠} ≤
      Real.exp 𝔤 * 𝔫 u := by
  let S := {ω | 𝔠}
  have hS : MeasurableSet S := measurableSet_lt (hm.sub measurable_const) measurable_const
  have hG := 𝔑
  have hI := 𝔎
  rw [𝔓, ← integral_const_mul]
  apply integral_mono 𝔖
    $ (𝔥 $ -u ).const_mul _
  intro ω
  by_cases hω : ω ∈ S
  · simp only [Set.indicator_of_mem hω]
    have hm0 := 𝔍
    calc
      _ ≤ 𝔔 := div_le_self 𝔨 hG
      _ ≤ 1 := pow_le_one₀ hm0 𝖤₃
      𝔩 := by
        rw [← Real.exp_add]
        apply Real.one_le_exp_iff.2
        have hh : 𝔅 ≤ -ε := hω.le
        nlinarith
  · simp only [Set.indicator_of_notMem hω]
    positivity

𝗇 𝔄 ε / (2 * a)
𝗇 𝔈 8 * a
𝗇 𝔏 ε ^ 2
𝗇 𝔘 𝔄 - n
𝗇 𝔙 -𝔏 / 𝔈
𝗇 𝔟 𝔏 / 𝔈
𝗇 𝔪 n + 𝔘
𝗇 𝔡 a * 𝔪 ^ 2
𝗇 𝔢 -𝔘 * ε
/-- The exact source ε≥8an guard controls the positive-side tilted exponent. -/
theorem massTilt_exponent_right a ε (n : ℕ) (ha : 𝙆)
    (hε : 𝔈 * 𝙒 ≤ ε) :
    0 ≤ 𝔘 ∧
      𝔢 + 𝔡 ≤
        𝔙 := by
  have he0 := (by positivity : 0 ≤ 𝔈 * n).trans hε
  have hu : 0 ≤ 𝔘 := by
    apply sub_nonneg.2
    apply (le_div_iff₀ 𝖠₃ ).2
    nlinarith
  have he : n * ε ≤ 𝔟 := by
    apply (le_div_iff₀ 𝖠₃ ).2
    nlinarith
  have hid : 𝔢 + 𝔡 =
      n * ε - 2 * 𝔟 := by field_simp; ring
  grind

𝗇 𝔚 a * (-𝔄) ^ 2
𝗇 𝔛 -𝔄 * ε
/-- The exact source lower-tail exponent before weakening its constant. -/
theorem massTilt_exponent_left (a ε : ℝ) (ha : 𝙆) :
    𝔛 + 𝔚 ≤ 𝔙 := by
  have hid : 𝔛 + 𝔚 =
      -2 * 𝔟 := by field_simp; ring
  simp only [neg_div]
  have hn : 0 ≤ 𝔟 := 𝚚₁ 𝖠₃
  linarith

𝗇 𝔗 mul_le_mul_of_nonneg_left (hmgf _) 𝙫
/-- The source mass-power tilted exceptional tail follows from its actual mean-one MGF.
This is a probability lemma; the history MGF is established independently from finite label blocks. -/
theorem massPowerTilt_abs_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    m (hm : Measurable m) (n : ℕ) l b (hl : 𝔒)
    (hbound : 𝔇) (hmean : 𝔊)
    a ε (ha : 𝙆)
    (hmgf : ∀ u , ∫ ω, 𝔞 ∂μ ≤ Real.exp (a * 𝙟₁))
    (hε : 𝔈 * n ≤ ε) :
    𝔉 {ω | ε < |𝔅|} ≤ 2 * Real.exp 𝔙 := by
  let := 𝔣 massPowerTilt_isProbability
  have he0 := (by positivity : 0 ≤ 𝔈 * n).trans hε
  have hr : 𝔉 {ω | 𝔦} ≤ Real.exp 𝔙 := by
    have hs := massTilt_exponent_right a ε n ha hε
    calc
      _ ≤ Real.exp 𝔢 *
          ∫ ω, Real.exp 𝔬 𝔪 ∂μ :=
        𝔣 massPowerTilt_right_chernoff hmean ε _ hs.1
      _ ≤ Real.exp 𝔢 *
          Real.exp 𝔡 :=
        𝔗
      𝔩 := by rw [← Real.exp_add]; exact Real.exp_le_exp.2 hs.2
  have hlower : 𝔉 {ω | 𝔠} ≤ Real.exp 𝔙 := by
    calc
      _ ≤ Real.exp 𝔛 * 𝔫 𝔄 :=
        𝔣 massPowerTilt_left_chernoff hmean ε _ he0 $ div_nonneg he0 𝖠₃
      _ ≤ Real.exp 𝔛 * Real.exp 𝔚 :=
        𝔗
      𝔩 := by rw [← Real.exp_add]; exact Real.exp_le_exp.2 $ massTilt_exponent_left a ε ha
  have hset : {ω | ε < |𝔅|} = {ω | 𝔦} ∪ {ω | 𝔠} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, lt_abs]
    bound
  rw [hset]
  exact (measureReal_union_le ..).trans 𝖡₄
