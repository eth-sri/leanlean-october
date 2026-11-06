module

public import NearlyMinimax.HighDesignEnergySeries
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! True selected normalized-design score energies. The squared likelihood
ratio cancels against the genuine response and design density, leaving
the source fixed denominator constant and the raw spatial numerator. -/
𝚴
𝚮
𝚨
𝚩
𝚭
𝚬

𝗇 𝔍 Measure.pi fun _ : κ => μ.restrict A
𝗃 𝔱 ἀ $ x i
section

variable [Fintype κ]
    [MeasurableSpace α]
    (μ : Measure α)
    [IsProbabilityMeasure μ]
    (f)
    (hf : Measurable f)
    (hprob : IsProbabilityMeasure $ μ.withDensity f )

include hf hprob

𝗇 𝔎 fun x => ∏ i, 𝔱 f
𝗇 𝔤 fun _ => μ.withDensity f
𝗃 𝔯 fun _ => ἀ
𝗃 𝔲 (s ἀ).indicator f
theorem fintype_probability_pi_withDensity :
    Measure.pi 𝔤 =
      (Measure.pi fun _ : κ => μ ).withDensity 𝔎 := by
  let _ := hprob
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ $ MeasurableSet.univ_pi hs , ← lintegral_indicator]
  · have he x :
        (Set.pi Set.univ s).indicator 𝔎 x =
          ∏ i, 𝔲 i (x i) := by
      by_cases h : ∀ i, x i ∈ s i
      · simp_all
      · obtain ⟨i, hi⟩ := not_forall.mp h
        have hz : ∏ j, 𝔲 j (x j) = 0 :=
          𝗈₁ $ Set.indicator_of_notMem hi f
        simp_all
    simp_rw [he]
    let G := fun i => 𝔲 i
    have hG := fun i => hf.indicator $ hs i
    rw [𝗒]
    apply Finset.prod_congr rfl
    intro i _
    rw [(measurePreserving_eval 𝔯 μ i).lintegral_comp $ hG i ]
    aesop
  · exact MeasurableSet.univ_pi hs

theorem fintype_probability_pi_restrict_withDensity A (hA : MeasurableSet A) :
    Measure.pi (fun _ => (μ.withDensity f).restrict A) =
      (𝔍).withDensity 𝔎 := by
  rw [← Measure.restrict_pi_pi 𝔤 𝔯 A,
    fintype_probability_pi_withDensity μ f hf hprob,
    restrict_withDensity $ MeasurableSet.univ_pi 𝔯 hA ,
    Measure.restrict_pi_pi]

end

𝗇 𝔈 𝔱 p
𝗇 𝔉 𝔱 q $ y i
𝗇 𝔔 κ → α
𝗇 𝔚 𝘬
𝗇 𝔠 κ → Fin 3
𝗃 𝔰 ∏ i, ἀ
def selectedRawLikelihood [Fintype κ]
    (p : 𝔚) (q : α → Fin 3 → ℝ) (x : 𝔔) (y : 𝔠) : ℝ :=
  𝔰 𝔈 * 𝔰 𝔉

𝗇 𝔏 (κ → α) → 𝔠 → ℝ
𝗇 𝔖 selectedRawLikelihood p q x y
𝗇 𝔡 R x y
def selectedConditionalScoreEnergy [Fintype κ]
    (p : 𝔚) (q : α → Fin 3 → ℝ)
    (R : 𝔏) (x : 𝔔) : ℝ :=
  ∑ y : 𝔠, 𝔰 𝔉 * (𝔡 / 𝔖) ^ 2

def selectedRawSquareEnergy [Fintype κ]
    (R : 𝔏) (x : 𝔔) : ℝ :=
  ∑ y : 𝔠, 𝔡 ^ 2

section

variable [Fintype κ]

𝗇 𝔢 selectedConditionalScoreEnergy p q R
𝗇 𝔒 𝔢 x
𝗇 𝔪 q x y
theorem selected_conditional_score_energy_nonneg (p : 𝔚) q (hq : ∀ x y, 0 ≤ 𝔪)
    R (x : 𝔔) :
    0 ≤ 𝔒 :=
  Finset.sum_nonneg fun y _ => mul_nonneg (Finset.prod_nonneg fun i _ => hq .. ) $ sq_nonneg _

𝗃 𝔫 fun i _ => ἀ i
𝗃 𝔭 0 < ἀ
theorem selected_raw_likelihood_positive (p : 𝔚) q (x : 𝔔) y
    (hp : ∀ i, 𝔭 𝔈) (hq : ∀ i, 𝔭 𝔉) :
    𝔭 𝔖 :=
  mul_pos (Finset.prod_pos 𝔫 hp) $ Finset.prod_pos 𝔫 hq

𝗇 𝔄 ∑ y : 𝔠, (m ^ Fintype.card κ * selectedRawLikelihood p q x y)⁻¹ * 𝔡 ^ 2
𝗇 𝔦 ∏ i, 𝔈 / m
theorem selected_score_density_cancel (m : ℝ) (hm : 𝔭 m) (p : 𝔚) q
    R x
    (hp : ∀ i, 𝔭 𝔈) (hq : ∀ i y, 0 < 𝔱 q y) :
    𝔦 * 𝔒 =
      𝔄 := by
  unfold selectedConditionalScoreEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  simp
  unfold selectedRawLikelihood
  field_simp

𝗇 𝔐 highFixedScoreDenominator pMinus cMass ^ Fintype.card κ
𝗇 𝔛 pMinus ^ 2 * cMass
𝗇 𝔧 m ^ Fintype.card κ * 𝔖
𝗇 𝔨 m * (𝔈 * 𝔉)
theorem selected_raw_inverse_floor (m pMinus cMass : ℝ) (hpMinus : 𝔭 pMinus) (hcMass : 𝔭 cMass)
    (hm : pMinus ≤ m) (p : 𝔚) q
    (x : 𝔔) y
    (hp : ∀ i, pMinus ≤ 𝔈) (hq : ∀ i, cMass ≤ 𝔉) :
    𝔧⁻¹ ≤
      𝔐 := by
  have hfac i : 𝔛 ≤ 𝔨 := by
    have hpq := mul_le_mul (hp i) (hq i) hcMass.le $ hpMinus.le.trans $ hp i
    have hh := mul_le_mul hm hpq (mul_nonneg hpMinus.le hcMass.le) $ hpMinus.le.trans hm
    nlinarith
  have hprod : 𝔛 ^ Fintype.card κ ≤
      𝔧 := by
    calc
      _ = ∏ _i : κ, 𝔛 := 𝖢₄
      _ ≤ 𝔰 𝔨 :=
        Finset.prod_le_prod₀ fun _ _ => by positivity 𝔫 hfac
      𝘿 := by unfold selectedRawLikelihood; simp [Finset.prod_mul_distrib]
  unfold highFixedScoreDenominator
  rw [inv_pow]
  bound

𝗇 𝔗 ∀ x ∈ A, ∀ y, 𝔭 𝔪
𝗃 𝔣 ἀ _ $ hx i
𝗇 𝔘 fun i => 𝔣 hp
𝗇 𝔙 fun i => Measure.tendsto_eval_ae_ae.eventually $ ae_restrict_mem hA
𝗇 𝔜 ∏ i, ENNReal.ofReal (𝔈 / m)
𝗇 𝔞 ∀ᵐ x ∂ 𝔍, ∀ i, x i ∈ A
𝗇 𝔥 ∀ x ∈ A, 0 < p x
𝗃 𝔬 fun x => ἀ
theorem normalized_selected_score_density_cancel_ae [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    A (hA : MeasurableSet A) m (hm : 𝔭 m)
    p q
    R
    (hp : 𝔥) (hq : 𝔗) :
    (fun x => (𝔜).toReal *
      𝔒) =ᵐ[𝔍]
      𝔬 𝔄 := by
  have hmem : 𝔞 :=
    ae_all_iff.mpr 𝔙
  filter_upwards [hmem] with x hx
  have he : (𝔜).toReal = 𝔦 := by
    rw [ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro i hi
    exact ENNReal.toReal_ofReal $ div_nonneg (𝔣 hp).le hm.le
  rw [he]
  exact selected_score_density_cancel m hm p q R x 𝔘
     fun i y => 𝔣 hq y

𝗇 𝔅 Measure.pi fun _ => (μ.withDensity fun z => ENNReal.ofReal $ p z / m ).restrict A
𝗇 𝔇 𝘯₁
𝗇 𝔊 fun x => ENNReal.ofReal $ p x / m
𝗇 𝔑 Filter.Eventually.of_forall fun _ => ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top
𝗇 𝔓 Finset.measurable_prod _ fun i _ => hf.comp $ measurable_pi_apply i
𝗇 𝔟 ∫ x, 𝔒 ∂ 𝔅
𝗇 𝔩 fintype_probability_pi_restrict_withDensity μ _ hf hprob A hA
𝗃 𝔳 normalized_selected_score_density_cancel_ae μ A hA m ἀ p q R
theorem normalized_selected_score_energy_integral_eq_raw [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    A (hA : MeasurableSet A) m (hm : 𝔭 m)
    p (hpMeas : Measurable p) q
    R
    (hprob : IsProbabilityMeasure $ μ.withDensity 𝔊 )
    (hp : 𝔥) (hq : 𝔗) :
    𝔟 =
      ∫ x, 𝔄
          ∂ 𝔇 := by
  have hf : Measurable 𝔊 :=
    ENNReal.measurable_ofReal.comp $ hpMeas.div_const m
  rw [𝔩]
  have hfP : Measurable fun x : 𝔔 => 𝔜 :=
    𝔓
  have he := integral_withDensity_eq_integral_toReal_smul
    (μ := 𝔇) hfP
    𝔑
    𝔢
  rw [he]
  apply integral_congr_ae
  exact 𝔳 hm hp hq

𝗃 𝔮 fun i => 𝔣 ἀ $ y i
theorem normalized_selected_score_energy_integrable_bound [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    A (hA : MeasurableSet A) m pMinus cMass
    (hpMinus : 𝔭 pMinus) (hcMass : 𝔭 cMass) (hm : pMinus ≤ m)
    p (hpMeas : Measurable p) q
    (hqMeas : ∀ y, Measurable 𝔬 𝔪)
    (R : 𝔏) (hR : ∀ y, Measurable 𝔬 𝔡)
    (hprob : IsProbabilityMeasure $ μ.withDensity 𝔊 )
    (hp : ∀ x ∈ A, pMinus ≤ p x) (hq : ∀ x ∈ A, ∀ y, cMass ≤ 𝔪)
    (hRaw : Integrable (selectedRawSquareEnergy R) 𝔇) :
    Integrable 𝔢
      𝔅 ∧
    𝔟 ≤
      𝔐 *
        ∫ x, selectedRawSquareEnergy R x ∂ 𝔇 := by
  have hm0 := hpMinus.trans_le hm
  have hpp x hx := hpMinus.trans_le $ hp x hx
  have hqp x hx y := hcMass.trans_le $ hq x hx y
  let W := 𝔬 𝔄
  have hWMeas : Measurable W := by
    apply Finset.measurable_sum
    unfold selectedRawLikelihood
    fun_prop
  have hmem : 𝔞 :=
    ae_all_iff.mpr 𝔙
  have hWbound : ∀ᵐ x ∂ 𝔇,
      0 ≤ W x ∧ W x ≤ 𝔐 * selectedRawSquareEnergy R x := by
    filter_upwards [hmem] with x hx
    constructor
    · apply Finset.sum_nonneg
      intro y hy
      have hL := selected_raw_likelihood_positive p q x y (fun i => 𝔣 hpp)
        𝔮 hqp
      positivity
    · unfold W selectedRawSquareEnergy
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro y hy
      exact mul_le_mul_of_nonneg_right
        (selected_raw_inverse_floor m pMinus cMass hpMinus hcMass hm p q x y
          𝔘 𝔮 hq) $ sq_nonneg _
  have hJ := hRaw.const_mul 𝔐
  have hWI : Integrable W 𝔇 := by
    apply hJ.mono' hWMeas.aestronglyMeasurable
    filter_upwards [hWbound] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  constructor
  · have hf : Measurable 𝔊 :=
      ENNReal.measurable_ofReal.comp $ hpMeas.div_const m
    rw [𝔩]
    apply (integrable_withDensity_iff_integrable_smul' 𝔓
      𝔑).mpr
    have he := 𝔳 hm0 hpp hqp
    exact hWI.congr he.symm
  rw [normalized_selected_score_energy_integral_eq_raw μ A hA m hm0 p hpMeas q R hprob hpp hqp]
  calc
    _ ≤ ∫ x, 𝔐 * selectedRawSquareEnergy R x
        ∂ 𝔇 :=
      integral_mono_ae hWI hJ $ hWbound.mono fun x hx => hx.2
    𝘿 := integral_const_mul ..
