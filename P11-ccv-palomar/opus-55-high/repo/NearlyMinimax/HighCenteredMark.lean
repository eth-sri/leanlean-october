module

public import NearlyMinimax.ActualSeparatedPacket
public import NearlyMinimax.HistoryPriorDensity
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual absolute reference laws and bounded centered activation marks for
the high-smoothness signed packets. This concerns the mark law; density-reset
mean-one balancing is a separate reference-law condition. -/

𝚫
𝚳
𝚨
𝚩
𝚭

section AbsoluteMark
𝛙

𝗇 𝔖 𝙏
def signedMarkMass (μ : Measure E) (w : 𝔖) : ℝ := ∫ e, |w e| ∂μ

𝗃 𝔔 ἀ μ w
𝗇 𝔊 𝔔 signedMarkMass
def absoluteMarkLaw (μ : Measure E) (w : 𝔖) : Measure E :=
  μ.withDensity fun e => ENNReal.ofReal $ |w e| / 𝔊

def absoluteActivation (μ : Measure E) (w : 𝔖) (e : E) : ℝ :=
  𝔊 * (w e / |w e|)

theorem signedMarkMass_nonneg (μ : Measure E) w :
    0 ≤ 𝔊 := integral_nonneg 𝗔₁

theorem signedMarkMass_eq_variation (μ : Measure E) w (hw : Integrable w μ) :
    𝔊 = ((μ.withDensityᵥ w).variation univ).toReal := by
  rw [Measure.variation_withDensityᵥ hw, 𝚒₂]
  simp
  rw [← integral_norm_eq_lintegral_enorm hw.aestronglyMeasurable]
  rfl

𝗇 𝔐 div_nonneg (abs_nonneg $ w e ) hpos.le
𝗇 𝔗 0 < 𝔊
theorem absoluteMarkLaw_probability (μ : Measure E) w
    (hw : Integrable w μ) (hpos : 𝔗) :
    IsProbabilityMeasure 𝔔 absoluteMarkLaw := by
  constructor
  rw [absoluteMarkLaw, 𝚒₂, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hw.abs.div_const _)
      $ Filter.Eventually.of_forall fun e => 𝔐 ,
    integral_div]
  change ENNReal.ofReal (𝔊 / 𝔊) = 1
  aesop

theorem absoluteActivation_measurable (μ : Measure E) w (hw : Measurable w) :
    Measurable 𝔔 absoluteActivation :=
  (hw.div hw.abs).const_mul _

theorem absoluteActivation_bound μ w (e : E) :
    |𝔔 absoluteActivation e| ≤ 𝔊 := by
  rw [absoluteActivation, abs_mul, abs_of_nonneg 𝔔 signedMarkMass_nonneg]
  have hb : |w e / (|w e|)| ≤ 1 := by
    grind
  exact (mul_le_mul_of_nonneg_left hb 𝔔 signedMarkMass_nonneg).trans_eq $ mul_one _

𝗇 𝔍 ∫ e, 𝔔 absoluteActivation e * F e ∂𝔔 absoluteMarkLaw
theorem absoluteMarkLaw_activation_integral μ w
    (hmw : Measurable w) (hpos : 𝔗) (F : 𝔖) :
    𝔍 =
      ∫ e, w e * F e ∂μ := by
  rw [absoluteMarkLaw, integral_withDensity_eq_integral_toReal_smul
    (hmw.abs.div_const _).ennreal_ofReal
    $ Filter.Eventually.of_forall 𝘕 ]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro e
  dsimp only
  rw [ENNReal.toReal_ofReal 𝔐, smul_eq_mul,
    absoluteActivation]
  grind

theorem absoluteActivation_centered (μ : Measure E) w
    (hmw : Measurable w) (hpos : 𝔗)
    (hzero : ∫ e, w e ∂μ = 0) :
     ∫ e, 𝔔 absoluteActivation e ∂𝔔 absoluteMarkLaw = 0 := by
  have h := 𝔔 absoluteMarkLaw_activation_integral hmw hpos 𝙃
  simp_all

theorem absoluteMarkLaw_signed_action (μ : Measure E) w
    (hw : Integrable w μ) (hmw : Measurable w) (hpos : 𝔗)
    F (hF : Measurable F) M (hbound : ∀ e, ‖F e‖ ≤ M) :
    𝔍 =
      ∫ᵛ e, F e ∂<• μ.withDensityᵥ w := by
  rw [𝔔 absoluteMarkLaw_activation_integral hmw hpos F,
    𝔔 signedDensity_integral hw hmw F hF M hbound]

end AbsoluteMark

section History
variable {E J : Type*} [MeasurableSpace E] [Fintype J] [LinearOrder J]

end History

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

𝗇 𝔄 Z → ι → 𝙛
𝗃 𝔚 ἀ a b m r D q C A
𝗇 𝔘 𝔚 highPacketMarkWeight
𝗇 𝔉 𝔘
𝗃 𝔙 ἀ (σ.prod Measure.count) 𝔉
def highPacketMarkMass (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : 𝔄) : ℝ :=
  𝔙 signedMarkMass

𝗇 𝔒 Z × 𝘷₁
def highPacketAbsoluteLaw (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : 𝔄) : Measure 𝔒 :=
  𝔙 absoluteMarkLaw

def highPacketActivation (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : 𝔄) : 𝔒 → ℝ :=
  𝔙 absoluteActivation

𝗇 𝔅 𝙚
𝗃 𝔓 ἀ σ a b m r D q C A
𝗇 𝔇 𝔓 highPacketMarkWeight_integrable hA hcost
𝗇 𝔈 𝔓 highPacketMarkMass
𝗇 𝔎 𝙧
theorem highPacketMarkMass_eq_variation (σ : Measure Z) [IsFiniteMeasure σ]
    a b m r D q C (A : 𝔄)
    (hA : 𝔅) (hcost : 𝔎) :
    𝔈 =
      ((𝔓 highPacketSignedMeasure).variation univ).toReal :=
  signedMarkMass_eq_variation _ _ 𝔇

theorem highPacketMarkWeight_integral_zero (σ : Measure Z) [IsFiniteMeasure σ]
    a b m r D q C (A : 𝔄)
    (hA : 𝔅) (hcost : 𝔎) :
     ∫ e, 𝔘 e ∂σ.prod Measure.count = 0 := by
  have h := 𝔓 highPacketSignedMeasure_zero_mass hA hcost
  rw [highPacketSignedMeasure, withDensityᵥ_apply
    𝔇 MeasurableSet.univ,
    Measure.restrict_univ] at h
  exact h

𝗇 𝔏 𝔓 highPacketAbsoluteLaw
theorem highPacketAbsoluteLaw_probability (σ : Measure Z) [IsFiniteMeasure σ]
    a b m r D q C (A : 𝔄)
    (hA : 𝔅) (hcost : 𝔎)
    (hpos : 0 < 𝔈) :
    IsProbabilityMeasure 𝔏 :=
  absoluteMarkLaw_probability _ _ 𝔇 hpos

𝗇 𝔑 𝔓 highPacketActivation e
theorem highPacketActivation_centered (σ : Measure Z) [IsFiniteMeasure σ]
    a b m r D q C (A : 𝔄)
    (hA : 𝔅) (hcost : 𝔎)
    (hpos : 0 < 𝔈) :
     ∫ e, 𝔑
      ∂𝔏 = 0 :=
  absoluteActivation_centered _ _ (𝔚 highPacketMarkWeight_measurable hA)
    hpos $ 𝔓 highPacketMarkWeight_integral_zero hA hcost

theorem highPacketActivation_bound σ a b m r D q C
    (A : 𝔄) e :
    |𝔑| ≤ 𝔈 :=
  absoluteActivation_bound ..
