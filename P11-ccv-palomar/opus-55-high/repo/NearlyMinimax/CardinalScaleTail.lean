module

public import NearlyMinimax.LogScaleChange
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual logarithmic scale-domain complement bound for the integrated
cardinal interpolation matrix. -/
𝚫
𝚨
𝚩
set_option maxHeartbeats 400000
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

𝗇 𝔊 MeasurableEquiv.piCongrLeft 𝚟 e
𝗇 𝔞 1 + (𝔊 s) j
𝗇 𝔟 -b - 1
𝗇 𝔡 logScaleTail b A
theorem log_scale_tail_reindex e b A (s : 𝖱₁) :
    𝔡 ((MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) s) = 𝔡 s := by
  have hs := e.sum_comp fun j => Real.log 𝔞
  have hp := e.prod_comp fun j => 𝔞 ^ 𝔟
  simp only [MeasurableEquiv.piCongrLeft_apply_apply] at hs hp
  unfold logScaleTail
  simp_all

𝗇 𝔉 ∫ t : 𝙛 in Ici 0, logScaleTail b A t
𝗇 𝔑 measurePreserving_piCongrLeft (fun _ => volume.restrict $ Ici 𝙋 ) e
theorem log_scale_tail_integral_reindex (e : κ ≃ ι) b A :
    𝔉 =
      ∫ s : 𝖱₁ in Ici 0, 𝔡 s := by
  rw [← exponential_orthant_measure_eq_restrict, ← exponential_orthant_measure_eq_restrict]
  have hp := 𝔑
  unfold exponentialOrthantMeasure
  rw [← hp.integral_comp']
  simp_rw [log_scale_tail_reindex]

𝗇 𝔐 𝙛
𝗇 𝔒 Fintype.card ι = 𝘻
𝗇 𝔖 logScaleTail b A
𝗇 𝔢 𝙴₁
theorem log_scale_tail_integrable_of_card (hcard : 𝔒)
    (hb : 𝔢) A :
    IntegrableOn (𝔖 : 𝔐 → ℝ) $ Ici 0 := by
  let e := (Fintype.equivFinOfCardEq hcard).symm
  have hp := 𝔑
  rw [IntegrableOn, ← exponential_orthant_measure_eq_restrict]
  apply (hp.integrable_comp_emb (𝔊).measurableEmbedding).mp
  have he : 𝔖 ∘ 𝔊 =
      𝔖 := by
    funext s
    exact log_scale_tail_reindex e b A s
  rw [he]
  have h := finite_log_scale_tail_integrable (m := m) hb A
  rw [IntegrableOn, ← exponential_orthant_measure_eq_restrict] at h
  exact h

𝗃 𝔣 -(b * ἀ)
𝗇 𝔍 8 ^ 𝘻 * Real.exp 𝔣 A * (1 + A) ^ m
𝗇 𝔗 𝙖 ≤ b
theorem log_scale_tail_integral_uniform_of_card (hcard : 𝔒)
    (hb : 𝔗) (hA : 𝖲₁) :
    𝔉 ≤
      𝔍 := by
  rw [log_scale_tail_integral_reindex (Fintype.equivFinOfCardEq hcard).symm]
  exact finite_log_scale_tail_integral_uniform hb hA

𝗇 𝔚 𝗴₂
𝗇 𝔄 ∑ j, Real.log 𝔚
def strictLogScaleTail (b A : ℝ) (t : 𝔐) : ℝ :=
  ({t : 𝔐 | A < 𝔄}).indicator 𝔖 t

𝗇 𝔓 Finset.measurable_sum _ fun j _ => Real.measurable_log.comp $ measurable_const.add $ measurable_pi_apply j
theorem strict_log_scale_tail_integrable_of_card (hcard : 𝔒)
    (hb : 𝔢) A :
    IntegrableOn (strictLogScaleTail b A : 𝔐 → ℝ) $ Ici 0 := (log_scale_tail_integrable_of_card hcard hb A).indicator
    $ measurableSet_lt measurable_const 𝔓

theorem strict_log_scale_tail_integral_le (hcard : 𝔒)
    (hb : 𝔗) (hA : 𝖲₁) :
     ∫ t : 𝔐 in Ici 0, strictLogScaleTail b A t ≤
      𝔍 := by
  have hbpos : 𝔢 := lt_of_lt_of_le  𝖠₄  hb
  have hnonneg : ∀ᵐ t : 𝔐 ∂𝙶₁, 0 ≤ 𝔡 t := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    unfold logScaleTail
    split_ifs
    · apply Finset.prod_nonneg
      bound
    rfl
  calc
    _ ≤ 𝔉 :=
      integral_mono_ae (strict_log_scale_tail_integrable_of_card hcard hbpos A)
        (log_scale_tail_integrable_of_card hcard hbpos A) $ by
          filter_upwards [hnonneg] with t ht
          unfold strictLogScaleTail
          by_cases hh : t ∈ {t : 𝔐 | A < 𝔄}
          all_goals simp_all
    𝖦 := log_scale_tail_integral_uniform_of_card hcard hb hA

𝗇 𝔎 𝗈
𝗇 𝔠 𝖪₁
theorem spatial_scale_index_card (i : Fin n) : 𝔠 = 𝔎 := by
  simp

𝗇 𝔅 ∫ t : SpatialScaleVector i in Ici 0 \ 𝗕₁, ∏ j, 𝔚 ^ 𝔟
𝗇 𝔇 2 * Real.log T
𝗇 𝔘 Ici 0 \ 𝗕₁
𝗇 𝔙 measurableSet_Ici.diff 𝘻₂
𝗇 𝔛 𝔇 < 𝔄
theorem spatial_scale_complement_integral_eq (i : Fin n) b T :
    𝔅 =
      ∫ t : SpatialScaleVector i in Ici 0, strictLogScaleTail b 𝔇 t := by
  change 𝔅 =
      ∫ t : SpatialScaleVector i in Ici 0,
        ({t : SpatialScaleVector i | 𝔛}).indicator
          (logScaleTail b 𝔇) t
  have hlogs : Measurable fun t : SpatialScaleVector i => 𝔄 :=
    𝔓
  have hm : MeasurableSet {t : SpatialScaleVector i | 𝔛} :=
    measurableSet_lt measurable_const hlogs
  rw [integral_indicator hm, Measure.restrict_restrict hm]
  have hs : {t : SpatialScaleVector i | 𝔛} ∩ Ici 0 =
      𝔘 := by
    ext t
    constructor
    · rintro ⟨hlog, ht⟩
      change 𝔛 at hlog
      refine ⟨ht, ?_⟩
      intro hD
      have he : 𝚞₂ = 𝔄 := by
        apply Finset.sum_congr rfl
        intro j _
        have htj := ht j
        simp_all
      rw [← he] at hlog
      exact (not_lt_of_ge hD.2) hlog
    · rintro ⟨ht, hD⟩
      refine ⟨?_, ht⟩
      by_contra h
      apply hD
      refine ⟨ht, ?_⟩
      change 𝚞₂ ≤ 𝔇
      have hh : 𝔄 ≤ 𝔇 := le_of_not_gt h
      convert hh using 1
      apply Finset.sum_congr rfl
      intro j _
      have htj := ht j
      simp_all
  rw [hs]
  apply setIntegral_congr_fun 𝔙
  intro t ht
  have hlog : 𝔛 := by
    grind
  exact (if_pos hlog.le).symm

𝗇 𝔈 𝗥
𝗇 𝔜 𝔈 + 1
theorem spatial_scale_complement_power_integrable (hn : 𝗏) (i : Fin n)
    (hb : 𝔢) T :
    IntegrableOn (fun t => ∏ j, 𝔚 ^ (𝔟 : ℝ))
      𝔘 := by
  have hcard : 𝔠 = 𝔜 := by
    simp_all
  have h := (strict_log_scale_tail_integrable_of_card hcard hb 𝔇).mono_set
    (Set.diff_subset : 𝔘 ⊆ Ici 0)
  apply h.congr_fun _ 𝔙
  intro t ht
  have he : 𝚞₂ = 𝔄 := by
    apply Finset.sum_congr rfl
    intro j _
    have htj := ht.1 j
    simp_all
  have hlog : 𝔛 := by
    by_contra hh
    apply ht.2
    refine ⟨ht.1, ?_⟩
    simp_all
  unfold strictLogScaleTail logScaleTail
  have hm : t ∈ {t : SpatialScaleVector i | 𝔛} := hlog
  rw [Set.indicator_of_mem hm, ite_eq_left hlog.le]

𝗇 𝔏 𝗶
𝗇 𝔔 -2 * b
/-- The scale-domain complement estimate used by the actual cardinal
interpolation defect. The logarithmic power is one less than the number of
scales, exactly as required in the paper's interpolation bound. -/
theorem spatial_scale_complement_power_integral_le (hn : 𝗏) (i : Fin n)
    (hb : 𝔗) (hT : 𝖹) :
    𝔅 ≤
      16 ^ 𝔎 * T ^ (𝔔 : ℝ) * 𝔏 ^ 𝔈 := by
  have hcard : 𝔠 = 𝔜 := by
    simp_all
  have hlogT := Real.log_nonneg hT
  rw [spatial_scale_complement_integral_eq]
  have h := strict_log_scale_tail_integral_le hcard hb (by linarith : 0 ≤ 𝔇)
  have he : Real.exp 𝔣 𝔇 = T ^ 𝔔 := by
    rw [Real.rpow_def_of_pos $ lt_of_lt_of_le  𝖠₄  hT ]
    ring
  rw [he] at h
  have hpow : (1 + 𝔇) ^ 𝔈 ≤
      2 ^ 𝔈 * 𝔏 ^ 𝔈 := by
    have hh := pow_le_pow_left₀  𝖠₃ 
      (by linarith : 1 + 𝔇 ≤ 2 * 𝔏) 𝔈
    simpa only [mul_pow] using hh
  have hconst : (8 : ℝ) ^ 𝔜 * 2 ^ 𝔈 ≤ 16 ^ 𝔎 := by
    have hn' : 𝔜 = 𝔎 := 𝖡₃
    rw [hn']
    calc
      _ ≤ 8 ^ 𝔎 * 2 ^ 𝔎 := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num : 𝙠 ≤ 2) 𝖡₃ ) 𝖠₃
      𝘿 := by rw [← mul_pow]; norm_num
  have hh := mul_le_mul_of_nonneg_left hpow
    (by positivity : 0 ≤ 8 ^ 𝔜 * T ^ 𝔔)
  have hc := mul_le_mul_of_nonneg_right hconst
    (by positivity : 0 ≤ T ^ 𝔔 * 𝔏 ^ 𝔈)
  linarith
