module

public import NearlyMinimax.HighCenteredMark
public import NearlyMinimax.HighRawUpdates
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual positive reference-law balancing by a zero-weight constant reset. -/
open Set MeasureTheory ProbabilityTheory
𝚮
𝚨
𝚩
𝚱

def highCenterRadius (C : ModelConstants d) : ℝ :=
  min (1 - C.densityLower) (C.densityUpper - 1) / 2

𝗇 𝔍 C.densityUpper - C.densityLower
def highCenterMix (C : ModelConstants d) : ℝ :=
  highCenterRadius C / (2 * 𝔍)

theorem highCenterRadius_pos (C : ModelConstants d) : 0 < highCenterRadius C :=
  div_pos (lt_min (sub_pos.mpr C.densityLower_lt_one) $ sub_pos.mpr C.one_lt_densityUpper )
    𝖠₄

theorem highCenterRadius_le_margins (C : ModelConstants d) :
    2 * highCenterRadius C ≤ 1 - C.densityLower ∧
      2 * highCenterRadius C ≤ C.densityUpper - 1 := by
  dsimp [highCenterRadius]
  grind

theorem highCenterMix_mem (C : ModelConstants d) :
    0 < highCenterMix C ∧ highCenterMix C < 1 := by
  have hgap : 0 < 𝔍 := by
    linarith [C.densityLower_lt_one, C.one_lt_densityUpper]
  have hm := highCenterRadius_le_margins C
  constructor
  · exact div_pos (highCenterRadius_pos C) $ mul_pos  𝖠₄  hgap
  · apply (div_lt_iff₀ $ mul_pos  𝖠₄  hgap ).mpr
    nlinarith

𝗇 𝔅 1 - δ
def balancedResetAnchor (δ q : ℝ) : ℝ := (1 - δ * q) / 𝔅

𝗇 𝔖 balancedResetAnchor δ q
𝗇 𝔚 δ < 1
theorem balancedResetAnchor_identity δ q (hδ : 𝔚) :
    δ * q + 𝔅 * 𝔖 = 1 := by
  unfold balancedResetAnchor
  grind

𝗇 𝔎 𝚈
𝗇 𝔏 𝘔₂
𝗇 𝔛 δ * W ≤ r / 2
theorem balancedResetAnchor_margins a b r W δ q (hr : 0 < r)
    (hδ0 : 𝔎) (hδ1 : 𝔚) (ha : a + r ≤ 1) (hb : 1 + r ≤ b)
    (hW : 𝘅 ≤ W) (hδW : 𝔛) (hq : q ∈ 𝔏) :
    𝔅 * (𝔖 - a) ≥ r / 2 ∧
      𝔅 * (b - 𝔖) ≥ r / 2 := by
  have hi := balancedResetAnchor_identity δ q hδ1
  have hl : δ * (q - a) ≤ δ * W := mul_le_mul_of_nonneg_left  𝖤₃  hδ0
  have hu : δ * (b - q) ≤ δ * W := mul_le_mul_of_nonneg_left  𝖤₃  hδ0
  bound

theorem balancedResetAnchor_mem a b r W δ q (hr : 0 < r)
    (hδ0 : 𝔎) (hδ1 : 𝔚) (ha : a + r ≤ 1) (hb : 1 + r ≤ b)
    (hW : 𝘅 ≤ W) (hδW : 𝔛) (hq : q ∈ 𝔏) :
    𝔖 ∈ 𝔏 := by
  have hm := balancedResetAnchor_margins a b r W δ q hr hδ0 hδ1 ha hb hW hδW hq
  constructor <;> nlinarith

𝗇 𝔈 Icc (C.densityLower + 𝗙) $ C.densityUpper - 𝗙
/-- The manuscript's mixing constant is uniform in M. -/
theorem sourceBalancedResetAnchor_mem (C : ModelConstants d)
    M q (hM : 𝚌) (hmargin : 𝗙 ≤ highCenterRadius C)
    (hq : q ∈ 𝔈) :
    balancedResetAnchor (highCenterMix C) q ∈
      𝔈 := by
  have hr := highCenterRadius_pos C
  have hδ := highCenterMix_mem C
  have hm := highCenterRadius_le_margins C
  have hg : 𝔍 ≠ 0 := by
    linarith
  apply balancedResetAnchor_mem _ _ (highCenterRadius C)
    𝔍 (highCenterMix C) q hr hδ.1.le hδ.2
  · linarith
  · linarith
  · linarith [one_div_pos.mpr hM]
  · dsimp [highCenterMix]
    field_simp
    linarith
  · exact hq

𝗇 𝔠 Sum.inr ()
𝗇 𝔉 Measure.dirac 𝔠
𝗇 𝔊 E ⊕ Unit
def balancedReferenceLaw [MeasurableSpace E] (μ : Measure E) (δ : ℝ) :
    Measure 𝔊 :=
  ENNReal.ofReal δ • μ.map Sum.inl + ENNReal.ofReal 𝔅 • 𝔉

𝗇 𝔇 balancedReferenceLaw μ δ
𝗇 𝔗 δ ≤ 1
theorem balancedReferenceLaw_probability [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] δ (hδ0 : 𝔎) (hδ1 : 𝔗) :
    IsProbabilityMeasure 𝔇 := by
  constructor
  rw [balancedReferenceLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply measurable_inl MeasurableSet.univ]
  simp
  rw [← ENNReal.ofReal_add hδ0 $ sub_nonneg.mpr hδ1 ]
  simp

𝗇 𝔐 𝙏
𝗇 𝔜 𝔊 → ℝ
def balancedIntercept (B : 𝔐) (δ q : ℝ) : 𝔜 :=
  Sum.elim B fun _ => 𝔖

𝗇 𝔘 𝖾
def balancedSlope (A : 𝔐) : 𝔜 := Sum.elim A 𝔘

𝗇 𝔒 w e / δ
𝗃 𝔢 fun e => ἀ
def balancedActivation (w : 𝔐) (δ : ℝ) : 𝔜 :=
  Sum.elim 𝔢 𝔒 𝔘

𝗇 𝔄 F $ Sum.inl e
𝗇 𝔙 Integrable 𝔢 𝔄 μ
𝗇 𝔞 (integrable_map_measure hF.aestronglyMeasurable measurable_inl.aemeasurable).mpr hFi
theorem balancedReferenceLaw_integrable [MeasurableSpace E]
    (μ : Measure E) (δ : ℝ) (F : 𝔜) (hF : Measurable F)
    (hFi : 𝔙) :
    Integrable F 𝔇 := by
  have hm :=
    𝔞
  have hd : Integrable F 𝔉 :=
    integrable_dirac' hF.stronglyMeasurable $ by finiteness
  exact integrable_add_measure.mpr ⟨hm.smul_measure ENNReal.ofReal_ne_top,
    hd.smul_measure ENNReal.ofReal_ne_top⟩

theorem balancedReferenceLaw_integral [MeasurableSpace E]
    (μ : Measure E) δ (hδ0 : 𝔎) (hδ1 : 𝔗)
    F (hF : Measurable F)
    (hFi : 𝔙) :
    ∫ e, F e ∂𝔇 =
      δ * ∫ e, 𝔄 ∂μ + 𝔅 * F 𝔠 := by
  have hm :=
    𝔞
  have hd : Integrable F 𝔉 :=
    integrable_dirac' hF.stronglyMeasurable $ by finiteness
  rw [balancedReferenceLaw, integral_add_measure
    (hm.smul_measure ENNReal.ofReal_ne_top) $ hd.smul_measure ENNReal.ofReal_ne_top ,
    integral_smul_measure, integral_smul_measure,
    integral_map measurable_inl.aemeasurable hF.aestronglyMeasurable,
    integral_dirac' _ _ hF.stronglyMeasurable,
    ENNReal.toReal_ofReal hδ0, ENNReal.toReal_ofReal $ sub_nonneg.mpr hδ1 ]
  rfl

theorem balancedIntercept_measurable [MeasurableSpace E]
    (B : 𝔐) (hB : Measurable B) δ q : Measurable $ balancedIntercept B δ q :=
  hB.sumElim measurable_const

theorem balancedSlope_measurable [MeasurableSpace E]
    (A : 𝔐) (hA : Measurable A) : Measurable $ balancedSlope A :=
  hA.sumElim measurable_const

𝗇 𝔡 balancedActivation w δ
theorem balancedActivation_measurable [MeasurableSpace E]
    (w : 𝔐) (hw : Measurable w) δ : Measurable 𝔡 :=
  (hw.div_const δ).sumElim measurable_const

𝗃 𝔣 ∫ e, ἀ e ∂μ
𝗇 𝔑 𝔣 B
theorem balancedIntercept_integral_one [MeasurableSpace E]
    (μ : Measure E) δ (hδ0 : 𝔎) (hδ1 : 𝔚)
    B (hB : Measurable B) (hBi : Integrable B μ) :
    ∫ e, balancedIntercept B δ 𝔑 e ∂𝔇 = 1 := by
  rw [balancedReferenceLaw_integral μ δ hδ0 hδ1.le _
    (balancedIntercept_measurable B hB ..) hBi]
  exact balancedResetAnchor_identity δ _ hδ1

theorem balancedSlope_integral_zero [MeasurableSpace E]
    (μ : Measure E) δ (hδ0 : 𝔎) (hδ1 : 𝔗)
    A (hA : Measurable A) (hAi : Integrable A μ) (hcenter : 𝔣 A = 0) :
    ∫ e, balancedSlope A e ∂𝔇 = 0 := by
  rw [balancedReferenceLaw_integral μ δ hδ0 hδ1 _ (balancedSlope_measurable A hA) hAi]
  simp only [balancedSlope, Sum.elim_inl, Sum.elim_inr, hcenter, mul_zero, add_zero]

𝗇 𝔓 𝔡 e
theorem balancedActivation_bound w δ W (hδ : 𝙮₂) (hW0 : 0 ≤ W)
    (hW : ∀ e, |w e| ≤ W) (e : 𝔊) : |𝔓| ≤ W / δ := by
  cases e with
  | inl e =>
    change |𝔒| ≤ _
    rw [abs_div, abs_of_pos hδ]
    exact div_le_div_of_nonneg_right (hW e) hδ.le
  | inr e =>
    change |0| ≤ _
    simpa only [abs_zero] using div_nonneg hW0 hδ.le

𝗇 𝔔 w e * 𝔄
theorem balancedActivation_integral [MeasurableSpace E]
    (μ : Measure E) δ (hδ : 𝙮₂) (hδ1 : 𝔗)
    w (hw : Measurable w) F (hF : Measurable F)
    (hWF : Integrable 𝔢 𝔔 μ) :
    ∫ e, 𝔓 * F e ∂𝔇 =
      ∫ e, 𝔔 ∂μ := by
  have hFi : Integrable (fun e => 𝔡 (Sum.inl e) * 𝔄) μ := by
    convert hWF.div_const δ using 1
    funext e
    change 𝔒 * 𝔄 = 𝔔 / δ
    ring
  rw [balancedReferenceLaw_integral μ δ hδ.le hδ1 (fun e => 𝔓 * F e)
    ((balancedActivation_measurable w hw δ).mul hF) hFi]
  simp only [balancedActivation, Sum.elim_inl, Sum.elim_inr, zero_mul, mul_zero, add_zero]
  have he : (fun e => 𝔒 * 𝔄) =
       fun e => 𝔔 / δ := 𝖧₃
  rw [he, integral_div]
  field_simp

theorem balancedActivation_integral_zero [MeasurableSpace E]
    (μ : Measure E) δ (hδ : 𝙮₂) (hδ1 : 𝔗)
    w (hw : Measurable w) (hwi : Integrable w μ) (hc : 𝔣 w = 0) :
    ∫ e, 𝔓 ∂𝔇 = 0 := by
  have hh := balancedActivation_integral μ δ hδ hδ1 w hw 𝙃 measurable_const
    𝖧₄
  simp_all

𝗇 𝔟 ∀ e, B e ∈ 𝔏
theorem boundedIntercept_integrable [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] B (hB : Measurable B)
    (a b : ℝ) (hb : 𝔟) : Integrable B μ := by
  apply (integrable_const $ max |a| |b| ).mono' hB.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro e
  rw [Real.norm_eq_abs]
  grind

theorem boundedIntercept_mean_mem [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] B (hB : Measurable B)
    (a b : ℝ) (hb : 𝔟) : 𝔑 ∈ 𝔏 := by
  have hBi := boundedIntercept_integrable μ B hB a b hb
  constructor
  · have hh := integral_mono (integrable_const a) hBi fun e => (hb e).1
    simp_all
  · have hh := integral_mono hBi (integrable_const b) fun e => (hb e).2
    simp_all
