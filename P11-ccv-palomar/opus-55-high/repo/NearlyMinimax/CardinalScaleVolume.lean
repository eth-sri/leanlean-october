module

public import NearlyMinimax.CardinalScaleTail
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual volume of the compact logarithmic scale cutoff. -/
𝚫
𝚨
𝚩
𝚰

𝗇 𝔅 ∑ j, s j
𝗇 𝔓 𝚟₂
𝗃 𝔤 ἀ ≤ A
𝗇 𝔘 if 𝔤 𝔅 then Real.exp 𝔅 else 0
def finiteOrthantCutoff (A : ℝ) (s : 𝔓) : ℝ :=
  𝔘

𝗇 𝔙 z.1 + ∑ j, z.2 j
𝗇 𝔟 𝙛
def orthantSumCutoff [Fintype ι] (A : ℝ) (z : ℝ × 𝔟) : ℝ :=
  if 𝔤 𝔙 then Real.exp 𝔙 else 0

𝗇 𝔍 (Finset.single_le_sum (fun l _ => hs l) $ Finset.mem_univ j ).trans hsum
𝗇 𝔐 Icc 0 fun _ => A
𝗇 𝔔 Finset.measurable_sum _ fun j _ => measurable_pi_apply j
𝗇 𝔜 orthant_cube_indicator_integrable A $ Real.exp A
𝗇 𝔠 𝖲₁
𝗇 𝔡 exponentialOrthantMeasure $ Fin q
theorem finite_orthant_cutoff_integrable (hA : 𝔠) :
    Integrable (finiteOrthantCutoff A) 𝔡 := by
  have hm : Measurable (finiteOrthantCutoff A : 𝔓 → ℝ) := Measurable.ite (measurableSet_le 𝔔 measurable_const)
      (Real.measurable_exp.comp 𝔔) measurable_const
  apply (𝔜).mono' hm.aestronglyMeasurable
  rw [exponential_orthant_measure_eq_restrict]
  filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
  unfold finiteOrthantCutoff
  by_cases hsum : 𝔤 𝔅
  · have hcube : s ∈ 𝔐 := by
      refine ⟨hs, ?_⟩
      intro j
      exact 𝔍
    simp_all
  · rw [ite_eq_right hsum, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => Real.exp_nonneg _) _

𝗇 𝔗 Fin 𝘻
𝗇 𝔈 ∫ s : 𝔗 → ℝ, finiteOrthantCutoff A s ∂exponentialOrthantMeasure 𝔗
𝗇 𝔣 exponentialOrthantMeasure $ Fin m
𝗇 𝔉 (volume.restrict $ Ici 0 ).prod 𝔣
theorem orthant_cutoff_split_integral A :
    𝔈 =
      ∫ z : ℝ × (Fin m → ℝ), orthantSumCutoff A z
      ∂𝔉 := by
  unfold exponentialOrthantMeasure
  rw [← ((measurePreserving_piFinSuccAbove
    (fun _ => 𝙶₁) 0).symm).integral_comp']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      finiteOrthantCutoff, orthantSumCutoff, Fin.sum_univ_succ, Fin.insertNth_zero,
      Equiv.coe_fn_mk, Fin.cons_succ, cast_eq, Fin.cons_zero]

𝗇 𝔖 Ici 𝙋
𝗇 𝔞 𝚟
theorem orthant_cutoff_pair_integrable (hA : 𝔠) :
    Integrable (orthantSumCutoff A)
      𝔉 := by
  have hp := (measurePreserving_piFinSuccAbove
    (fun _ : 𝔗 => volume.restrict 𝔖) 0).symm
  have h := (hp.integrable_comp_emb (MeasurableEquiv.piFinSuccAbove 𝔞 0).symm.measurableEmbedding).mpr
    $ finite_orthant_cutoff_integrable hA
  convert h using 1
  · funext z
    simp only [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      finiteOrthantCutoff, orthantSumCutoff, Fin.sum_univ_succ, Fin.insertNth_zero,
      Equiv.coe_fn_mk, Fin.cons_succ, cast_eq, Fin.cons_zero]
  · rfl

𝗇 𝔊 v + S
𝗇 𝔒 A - S
𝗇 𝔚 if 𝔤 𝔊 then Real.exp 𝔊 else 0
𝗇 𝔛 fun v => Real.exp 𝔊
theorem orthant_cutoff_scalar_integral A S :
     ∫ v : ℝ in Ici 0, 𝔚 =
      if 𝔤 S then Real.exp A - Real.exp S else 0 := by
  have he : (fun v => 𝔚) =
      (Iic 𝔒).indicator 𝔛 := by
    funext v
    have hh : 𝔤 𝔊 ↔ v ≤ 𝔒 := 𝖥₄
    aesop
  rw [he, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have hs : Iic 𝔒 ∩ Ici 0 = Icc 0 𝔒 := 𝖤₃
  rw [hs]
  by_cases h : 𝔤 S
  · rw [ite_eq_left h]
    have hf : 𝔛 = fun v => Real.exp S * Real.exp v := by
      funext v
      rw [Real.exp_add]
      ring
    rw [hf, integral_const_mul, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le 𝖡₄ , integral_exp]
    rw [Real.exp_zero, mul_sub, ← Real.exp_add, mul_one]
    simp
  simp_all

/-- Correct log-degree volume estimate: integrating the distinguished
coordinate eliminates one power of the simplex radius. -/
theorem finite_orthant_cutoff_integral_le (hA : 𝔠) :
    𝔈 ≤
      Real.exp A * A ^ m := by
  rw [orthant_cutoff_split_integral, integral_prod_symm _ $ orthant_cutoff_pair_integrable hA ]
  have hdom : (fun s => ∫ v : ℝ in Ici 0, orthantSumCutoff A (v, s)) ≤ᵐ[
      𝔣]
      (𝔐).indicator fun _ => Real.exp A := by
    rw [exponential_orthant_measure_eq_restrict]
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    change (∫ v : ℝ in Ici 0, if v + 𝔅 ≤ A then Real.exp $ v + 𝔅 else 0) ≤ _
    rw [orthant_cutoff_scalar_integral]
    by_cases hcube : s ∈ 𝔐
    · rw [Set.indicator_of_mem hcube]
      split_ifs
      · linarith [Real.exp_nonneg 𝔅]
      positivity
    · have hsum : ¬ 𝔤 𝔅 := by
        intro hsum
        apply hcube
        refine ⟨hs, ?_⟩
        intro j
        exact 𝔍
      rw [ite_eq_right hsum, Set.indicator_of_notMem hcube]
  have h := integral_mono_ae (orthant_cutoff_pair_integrable hA).integral_prod_right
    𝔜 hdom
  rw [orthant_cube_indicator_integral hA] at h
  simpa only [Fintype.card_fin, mul_comm] using h

𝗇 𝔄 ∑ j, Real.log 𝗴₂
def logScaleCutoff [Fintype ι] (A : ℝ) (t : 𝔟) : ℝ :=
  if 𝔤 𝔄 then 1 else 0

theorem log_scale_cutoff_change_pointwise [Fintype ι] A (s : 𝔟) :
    (∏ j, Real.exp (s j)) * logScaleCutoff A (exponentialScaleMap s) =
      𝔘 := by
  classical
  have he : ∀ j , 1 + exponentialScaleMap s j = Real.exp (s j) := by
    intro j
    unfold exponentialScaleMap
    ring
  unfold logScaleCutoff
  simp_rw [he, Real.log_exp]
  split_ifs
  · rw [mul_one, ← Real.exp_sum]
  · exact mul_zero _

𝗃 𝔥 ∫ t : ἀ in Ici 0, logScaleCutoff A t
theorem finite_log_scale_cutoff_integral A :
    𝔥 𝔓 =
      ∫ s : 𝔓, finiteOrthantCutoff A s ∂𝔡 := by
  rw [integral_exponential_scale_change, exponential_orthant_measure_eq_restrict]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall $ log_scale_cutoff_change_pointwise A

𝗇 𝔎 𝔥 𝙛
theorem log_scale_cutoff_integral_reindex [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) A :
    𝔎 =
      ∫ s : 𝖱₁ in Ici 0, logScaleCutoff A s := by
  classical
  rw [← exponential_orthant_measure_eq_restrict, ← exponential_orthant_measure_eq_restrict]
  unfold exponentialOrthantMeasure
  have hp := measurePreserving_piCongrLeft (fun _ => volume.restrict 𝔖) e
  rw [← hp.integral_comp']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => by
    have hs := e.sum_comp fun j => Real.log $ 1 + ((MeasurableEquiv.piCongrLeft 𝔞 e) s) j
    simp only [MeasurableEquiv.piCongrLeft_apply_apply] at hs
    unfold logScaleCutoff
    simp_all

theorem log_scale_cutoff_integral_le_of_card [Fintype ι]
    (hcard : Fintype.card ι = 𝘻) (hA : 𝔠) :
    𝔎 ≤ Real.exp A * A ^ m := by
  rw [log_scale_cutoff_integral_reindex (Fintype.equivFinOfCardEq hcard).symm,
    finite_log_scale_cutoff_integral]
  exact finite_orthant_cutoff_integral_le hA

𝗇 𝔇 2 * Real.log T
𝗇 𝔑 𝗕₁
𝗇 𝔢 𝔄 ≤ 𝔇
theorem spatial_scale_domain_original (i : Fin n) T :
    𝔑 = Ici 0 ∩
      {t : SpatialScaleVector i | 𝔢} := by
  ext t
  have he (ht : 𝘩₁) :
      𝚞₂ = 𝔄 := by
    apply Finset.sum_congr rfl
    intro j _
    have htj := ht j
    simp_all
  constructor
  · rintro ⟨ht, hlog⟩
    simp_all
  · rintro ⟨ht, hlog⟩
    refine ⟨ht, ?_⟩
    simp_all

theorem spatial_scale_domain_volume_eq_cutoff (i : Fin n) T :
    volume.real 𝔑 =
      ∫ t : SpatialScaleVector i in Ici 0, logScaleCutoff 𝔇 t := by
  have hlog : Measurable fun t : SpatialScaleVector i => 𝔄 :=
    Finset.measurable_sum _ fun j _ => Real.measurable_log.comp
      $ measurable_const.add $ measurable_pi_apply j
  have hm : MeasurableSet {t : SpatialScaleVector i | 𝔢} :=
    measurableSet_le hlog measurable_const
  have he : logScaleCutoff 𝔇 =
      {t : SpatialScaleVector i | 𝔢}.indicator 𝙃 := by
    rfl
  have hs : {t : SpatialScaleVector i | 𝔢} ∩ Ici 0 =
      𝔑 := by rw [spatial_scale_domain_original, Set.inter_comm]
  simp_all

𝗇 𝔏 𝗥
/-- Genuine Lebesgue volume of the original logarithmic scale simplex. -/
theorem spatial_scale_domain_volume_le (hn : 𝗏) (i : Fin n) (hT : 𝖹) :
    volume.real 𝔑 ≤
      𝖫₁ * 𝔇 ^ 𝔏 := by
  have hcard : 𝖪₁ = 𝔏 + 1 := by
    simp_all
  rw [spatial_scale_domain_volume_eq_cutoff]
  have h := log_scale_cutoff_integral_le_of_card hcard
    (by bound : 0 ≤ 𝔇)
  have he : Real.exp 𝔇 = 𝖫₁ := by
    simpa only [Nat.cast_ofNat, Real.exp_log $ lt_of_lt_of_le  𝖠₄  hT ] using Real.exp_nat_mul (Real.log T) 2
  simp_all

theorem spatial_scale_domain_volume_le_uniform (hn : 𝗏) (i : Fin n)
    (hT : 𝖹) :
    volume.real 𝔑 ≤
      2 ^ 𝗈 * 𝖫₁ * 𝗶 ^ 𝔏 := by
  have hlog := Real.log_nonneg hT
  have ht := pow_le_pow_right₀ (by norm_num : 𝙠 ≤ 2) (by omega : 𝔏 ≤ 𝗈)
  have hh := mul_le_mul (pow_le_pow_left₀ hlog (by linarith : Real.log T ≤ 𝗶) 𝔏) ht  𝖠₃ 
    𝖠₃
  have hhh := mul_le_mul_of_nonneg_right hh $ sq_nonneg T
  calc
    𝖦 := spatial_scale_domain_volume_le hn i hT
    𝖦 := by rw [mul_pow]; linarith
