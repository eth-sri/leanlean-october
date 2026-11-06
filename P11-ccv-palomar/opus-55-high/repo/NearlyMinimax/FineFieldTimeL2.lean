module

public import NearlyMinimax.FinePairAllCounts
public import NearlyMinimax.HigherFieldMomentL2
public import NearlyMinimax.CardinalWeightedBounds
public import NearlyMinimax.SpatialSubsetEnergy
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Integration of the genuine higher field moments over the fine-row scale. -/
𝚴
𝚮
𝚨
𝚩

𝗇 𝔅 𝗲₂
𝗇 𝔞 ℝ × 𝔅
/-- The constructed field moment is jointly Borel in its scale and spatial tuple. -/
theorem boundedHyperplaneSpatialMoment_joint_measurable (d j : ℕ) [NeZero d] :
    Measurable fun z : 𝔞 => boundedHyperplaneSpatialMoment d z.1 j z.2 := by
  let κ : Kernel 𝔞 $ FinePairFieldMark d := (finePairFieldKernel d).comap Prod.fst measurable_fst
  have hm : Measurable fun z : 𝔞 × FinePairFieldMark d =>
      ∏ l, boundedHyperplaneFieldValue z.2 (z.1.2 l) :=
    Finset.measurable_prod _ fun l _ => (boundedHyperplaneFieldValue_measurable d).comp
      $ measurable_snd.prodMk $ (measurable_pi_apply l).comp $ measurable_snd.comp measurable_fst
  exact (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

𝗇 𝔒 T ^ d
def fineFieldScaleWeight (d : ℕ) (T : ℝ) : ℝ := T / 𝔒

𝗇 𝔊 Icc lo hi
𝗇 𝔓 𝙫₁
𝗇 𝔟 (pow_pos (hlo.trans_le hT.1) d).ne'
theorem fineFieldScaleWeight_continuousOn (hlo : 𝔓) :
    ContinuousOn (fineFieldScaleWeight d) 𝔊 := by
  apply continuousOn_id.div (continuous_pow d).continuousOn
  intro T hT
  exact 𝔟

theorem fineFieldScaleWeight_integrableOn (hlo : 𝔓) :
    IntegrableOn (fineFieldScaleWeight d) 𝔊 :=
  (fineFieldScaleWeight_continuousOn hlo).integrableOn_compact isCompact_Icc

𝗇 𝔈 T ^ (1 - 𝙊)
𝗇 𝔤 fineFieldScaleWeight d T
theorem fineFieldScaleWeight_eq_rpow (hT : 𝗹₁) :
    𝔤 = 𝔈 := by
  unfold fineFieldScaleWeight
  rw [Real.rpow_sub hT, Real.rpow_one, Real.rpow_natCast]

𝗇 𝔇 ∫ T in Icc lo hi, 𝔤
𝗇 𝔔 lo ^ (2 - 𝙊)
𝗇 𝔡 fun T => 𝔈
𝗇 𝔢 (3 : ℝ) ≤ d
theorem fineFieldScaleWeight_integral_le (hd : 3 ≤ d) (hlo : 𝔓) :
    𝔇 ≤ 𝔔 / (d - 2) := by
  have hdR : 𝔢 := by exact_mod_cast hd
  have hdec : 𝙠 - d < -1 := 𝖡₄
  have htail : IntegrableOn 𝔡 $ Ici lo := by
    change Integrable 𝔡 $ volume.restrict $ Ici lo
    rw [← Measure.restrict_congr_set Ioi_ae_eq_Ici]
    exact integrableOn_Ioi_rpow_of_lt hdec hlo
  have he : 𝔇 =
      ∫ T in 𝔊, 𝔈 := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro T hT
    exact fineFieldScaleWeight_eq_rpow $ hlo.trans_le hT.1
  rw [he]
  apply (integral_mono_measure (Measure.restrict_mono_set volume Icc_subset_Ici_self)
    (by filter_upwards [ae_restrict_mem measurableSet_Ici] with T hT; exact Real.rpow_nonneg (hlo.le.trans hT) _) htail).trans_eq
  rw [integral_Ici_eq_integral_Ioi]
  rw [integral_Ioi_rpow_of_lt hdec hlo]
  grind

𝗇 𝔄 (T,x)
𝗇 𝔛 pow_nonneg (hlo.le.trans hT.1) _
𝗇 𝔉 div_nonneg (hlo.le.trans hT.1) 𝔛
𝗇 𝔖 K ^ 2
𝗇 𝔘 ∫ T, ∫ x, g 𝔄 ∂mu ∂nu
𝗇 𝔙 (∫ T in 𝔊, T * F 𝔄) ^ 2
𝗃 𝔥 ∫ T, ἀ 𝔄 ∂nu
𝗇 𝔚 𝔥 f ^ 2
𝗃 𝔦 fun T => ἀ 𝔄
/-- Weighted Cauchy--Schwarz and genuine Fubini exchange for a bounded
jointly Borel spatial moment, integrated over a finite positive scale band. -/
theorem weighted_scale_square_energy_le [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (d : ℕ)
    (hlo : 𝔓) (hK : 𝖭₂) (F : ℝ × X → ℝ) (hF : Measurable F)
    (hFb : ∀ z, |F z| ≤ 1)
    (hE : ∀ T ∈ 𝔊, ∫ x, F 𝔄 ^ 2 ∂mu ≤ 𝔖 / 𝔒 ^ 2) :
    Integrable (fun x => 𝔙) mu ∧
       ∫ x, 𝔙 ∂mu ≤
        𝔖 * 𝔇 ^ 2 := by
  let nu := volume.restrict 𝔊
  let W := ∫ T, 𝔤 ∂nu
  let f := fun z => z.1 * F z
  let g := fun z => z.1 * z.1 ^ d * F z ^ 2
  have hw : Integrable (fineFieldScaleWeight d) nu := fineFieldScaleWeight_integrableOn hlo
  have hW : 0 ≤ W := integral_nonneg_of_ae $ by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
    exact 𝔉
  have hfm := measurable_fst.mul hF
  have hfi : Integrable f $ nu.prod mu :=
     ((continuous_id.continuousOn.integrableOn_compact isCompact_Icc).comp_fst mu).mul_bdd
      hF.aestronglyMeasurable $ Filter.Eventually.of_forall fun z => by
        bound
  have hgi : Integrable g $ nu.prod mu := by
    have ht : Integrable (fun T => T * 𝔒) nu :=
      (continuous_id.mul $ continuous_pow d ).continuousOn.integrableOn_compact isCompact_Icc
    apply (ht.comp_fst mu).mul_bdd (c := 1) (hF.pow_const 2).aestronglyMeasurable
    simp_all
  have hcs : ∀ᵐ x ∂mu, 𝔚 ≤ W * 𝔥 g := by
    filter_upwards [hfi.prod_left_ae, hgi.prod_left_ae] with x hfx hgx
    apply integral_square_le_weight_mass_mul nu 𝔦 f
      (fineFieldScaleWeight d) 𝔦 g hfx hw hgx
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
      exact 𝔉
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
      exact mul_nonneg (mul_nonneg (hlo.le.trans hT.1)
        𝔛) $ sq_nonneg _
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
      have hp := 𝔟
      dsimp [f, g, fineFieldScaleWeight]
      field_simp
      exact le_refl _
  have hsi : Integrable (fun x => 𝔚) mu := by
    apply (hgi.integral_prod_right.const_mul W).mono'
      (hfm.stronglyMeasurable.integral_prod_left'.measurable.pow_const 2).aestronglyMeasurable
    simpa
  have hbound := integral_mono_ae hsi (hgi.integral_prod_right.const_mul W) hcs
  rw [integral_const_mul] at hbound
  rw [ (integral_integral_swap hgi).symm ] at hbound
  have hi : 𝔘 ≤ 𝔖 * W := by
    have hm : 𝔘 ≤ ∫ T, 𝔖 * 𝔤 ∂nu := by
      apply integral_mono_ae hgi.integral_prod_left $ hw.const_mul 𝔖
      filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
      dsimp [g]
      rw [integral_const_mul]
      have hp := hlo.trans_le hT.1
      have h := mul_le_mul_of_nonneg_left (hE T hT)
        $ mul_nonneg hp.le $ pow_nonneg hp.le d
      apply h.trans_eq
      dsimp [fineFieldScaleWeight]
      field_simp
    exact hm.trans_eq $ integral_const_mul ..
  have hfinal := hbound.trans $ mul_le_mul_of_nonneg_left hi hW
  bound

𝗇 𝔠 finePairTimeSubsetMoment lo hi U Finset.univ
theorem finePairTimeSubsetMoment_univ_eq [NeZero d]
    (lo hi : ℝ) (U : 𝔅) :
    𝔠 =
      ∫ T in 𝔊, T * boundedHyperplaneSpatialMoment d T j U := by
  rw [finePairTimeSubsetMoment_actual]
  rfl

𝗇 𝔍 fullSpatialPatchDesign d j
𝗇 𝔎 hyperplaneSpatialMomentConstant d ^ j * j ^ 4
𝗇 𝔏 fun z => boundedHyperplaneSpatialMoment d z.1 j z.2
𝗇 𝔐 fun z => boundedHyperplaneSpatialMoment_abs_le_one d z.1 j z.2
𝗇 𝔑 integral_nonneg 𝖸
𝗇 𝔗 Real.sqrt (∫ U : 𝔅, boundedHyperplaneSpatialMoment d T j U ^ 2 ∂ 𝔍) ^ 2 ≤ (K / 𝔒) ^ 2
𝗇 𝔜 weighted_scale_square_energy_le 𝔍 d (hi := hi) hlo hK 𝔏 (boundedHyperplaneSpatialMoment_joint_measurable d j) 𝔐
/-- The actual time-mark integral is genuinely square integrable over Q^j. -/
theorem finePairTimeSubsetMoment_univ_square_integrable [NeZero d]
    (hd : 3 ≤ d) (hj : 𝙳₁) (hlo : 𝔓) :
    Integrable (fun U : 𝔅 =>
      𝔠 ^ 2) 𝔍 := by
  let K := 𝔎
  have hK : 𝖭₂ := by positivity [hyperplaneSpatialMomentConstant_positive d]
  have hh := 𝔜 fun T hT => by
      have hp := hlo.trans_le hT.1
      have hb := boundedHyperplaneSpatialMoment_L2_le d T hp j hj
      have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) 𝖠₃ ).mpr hb
      change 𝔗 at hs
      simpa only [Real.sq_sqrt 𝔑, div_pow] using hs
  simp_rw [finePairTimeSubsetMoment_univ_eq]
  exact hh.1

𝗇 𝔣 Real.rpow_nonneg hlo.le _
/-- True spatial decay after scale integration, for the fine row's actual
carrier and field law, rather than an assumed moment or time-energy bound. -/
theorem finePairTimeSubsetMoment_univ_L2_le [NeZero d]
    (hd : 3 ≤ d) (hj : 𝙳₁) (hlo : 𝔓) :
    Real.sqrt (∫ U : 𝔅,
      𝔠 ^ 2 ∂ 𝔍) ≤
      𝔎 * 𝔔 := by
  let K := 𝔎
  have hK : 𝖭₂ := by positivity [hyperplaneSpatialMomentConstant_positive d]
  have hh := 𝔜 fun T hT => by
      have hp := hlo.trans_le hT.1
      have hb := boundedHyperplaneSpatialMoment_L2_le d T hp j hj
      have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) 𝖠₃ ).mpr hb
      change 𝔗 at hs
      simpa only [Real.sq_sqrt 𝔑, div_pow] using hs
  have hW0 : 0 ≤ 𝔇 := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
    exact 𝔉
  have hW := fineFieldScaleWeight_integral_le hd hlo (hi := hi)
  have hdR : 𝔢 := by exact_mod_cast hd
  have hw :=
    hW.trans $ div_le_self 𝔣 𝖡₄
  have ht := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hW0 hw 2) $ sq_nonneg K
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg hK 𝔣, ?_⟩
  simp_rw [finePairTimeSubsetMoment_univ_eq]
  linarith
