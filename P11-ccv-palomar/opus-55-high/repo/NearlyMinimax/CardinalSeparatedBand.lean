module

public import NearlyMinimax.CardinalSeparatedKernel
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Genuine positive separated mark measures for interpolation bands. Two
positive copies with opposite symmetric matrix marks suffice; their cost
is bounded by twice the upper-cutoff cost. -/
𝚫
𝚨
𝚩
𝚱

𝗃 𝔧 ἀ d n
abbrev CardinalBandMark (d n : ℕ) := Bool × 𝔧 CardinalSeparatedMark

𝗇 𝔄 𝔧 cardinalSeparatedMeasure $ max 1 L
𝗇 𝔈 𝔧 CardinalBandMark
𝗇 𝔍 (false, z)
𝗇 𝔎 𝚠₂
𝗇 𝔏 (true, z)
𝗃 𝔣 fun z => ἀ
def cardinalBandMeasure (d n : ℕ) (L T : ℝ) : Measure 𝔈 :=
  Measure.map 𝔣 𝔍 𝔎 +
    Measure.map 𝔣 𝔏 𝔄

𝗇 𝔖 𝙮
def cardinalBandAmplitude (lam : ℝ) (z : 𝔈)
    (β β' : 𝔖) : ℝ :=
  if z.1 then -cardinalSeparatedAmplitude lam z.2 β β' else cardinalSeparatedAmplitude lam z.2 β β'

def cardinalBandFactor (lam : ℝ) (z : 𝔈)
    (l : Fin n) (x : Covariate d) : ℝ := cardinalSeparatedFactor lam z.2 l x

theorem cardinal_band_mark_standardBorel d n : StandardBorelSpace 𝔈 := by
  letI := 𝔧 cardinal_separated_mark_standardBorel
  infer_instance

𝗇 𝔅 𝔧 cardinalBandMeasure L T
𝗇 𝔉 le_max_left 1 L
𝗇 𝔛 𝖹
theorem cardinal_band_measure_finite d n L (hT : 𝔛) :
    IsFiniteMeasure 𝔅 := by
  letI := 𝔧 cardinal_separated_measure_finite hT
  letI := 𝔧 cardinal_separated_measure_finite 𝔉
  unfold cardinalBandMeasure
  infer_instance

𝗇 𝔟 (cardinal_separated_amplitude_measurable lam β β').comp measurable_snd
theorem cardinal_band_amplitude_measurable lam (β β' : 𝔖) :
    Measurable fun z : 𝔈 => cardinalBandAmplitude lam z β β' := by
  apply Measurable.ite
  · exact measurable_fst $ measurableSet_singleton true
  · exact (𝔟).neg
  · exact 𝔟

theorem cardinal_band_factor_measurable lam (l : Fin n) x :
    Measurable fun z : 𝔈 => cardinalBandFactor lam z l x :=
  (cardinal_separated_factor_measurable lam l x).comp measurable_snd

theorem cardinal_band_factor_abs_le_one lam (z : 𝔈)
    l x (hx : ∀ r, |x r| ≤ 2) : |cardinalBandFactor lam z l x| ≤ 1 :=
  cardinal_separated_factor_abs_le_one lam z.2 l x hx

𝗇 𝔙 (integrable_map_measure hf.aestronglyMeasurable (measurable_const.prodMk measurable_id).aemeasurable).mpr
𝗃 𝔨 fun z => f ἀ
𝗇 𝔜 Integrable 𝔨 𝔍 𝔎
𝗇 𝔞 Integrable 𝔨 𝔏 𝔄
theorem cardinal_band_integrable_of_copies L T
    (f : 𝔈 → ℝ) (hf : Measurable f)
    (hT : 𝔜)
    (hL : 𝔞) :
    Integrable f 𝔅 := by
  apply integrable_add_measure.mpr
  constructor
  · exact 𝔙 hT
  · exact 𝔙 hL

𝗃 𝔥 fun z : 𝔧 CardinalSeparatedMark => ἀ
theorem cardinal_band_integral_eq_copies L T
    (f : 𝔈 → ℝ) (hf : Measurable f)
    (hT : 𝔜)
    (hL : 𝔞) :
     ∫ z, f z ∂𝔅 =
       ∫ z, f 𝔍 ∂𝔎 +
         ∫ z, f 𝔏 ∂𝔄 := by
  have hmF : Measurable 𝔥 𝔍 := 𝖦₃
  have hmL : Measurable 𝔥 𝔏 := 𝖦₃
  have hiL :=
    (integrable_map_measure hf.aestronglyMeasurable hmL.aemeasurable).mpr hL
  unfold cardinalBandMeasure
  rw [integral_add_measure ((integrable_map_measure hf.aestronglyMeasurable hmF.aemeasurable).mpr hT) hiL,
    integral_map hmF.aemeasurable hf.aestronglyMeasurable,
    integral_map hmL.aemeasurable hf.aestronglyMeasurable]

𝗃 𝔦 ἀ (D := D)
𝗇 𝔐 𝔦 cardinalBandAmplitude lam
theorem cardinal_band_cost_eq lam (z : 𝔈) :
    separatedMatrixCost 𝔐 z =
      separatedMatrixCost (𝔦 cardinalSeparatedAmplitude lam) z.2 := by
  unfold separatedMatrixCost cardinalBandAmplitude
  bound

𝗇 𝔇 separatedMatrixCost $ cardinalBandAmplitude (d := d) (n := n) (D := D) lam
𝗇 𝔊 Finset.measurable_fun_sum _ fun β _ => Finset.measurable_fun_sum _ fun β' _ => (cardinal_band_amplitude_measurable lam β β').abs
theorem cardinal_band_cost_integrable lam L (hT : 𝔛) :
    Integrable (separatedMatrixCost 𝔐) 𝔅 := by
  have hm : Measurable 𝔇 :=
    𝔊
  apply cardinal_band_integrable_of_copies L T _ hm
  · simpa only [cardinal_band_cost_eq] using cardinal_separated_cost_integrable lam hT
  · simpa only [cardinal_band_cost_eq] using cardinal_separated_cost_integrable lam 𝔉

𝗇 𝔒 max 1 L
𝗇 𝔡 𝗥
𝗇 𝔔 𝗶 ^ 𝔡
𝗇 𝔗 𝗈
theorem cardinal_band_cost_integral_le (hn : 𝗏) lam L
    (hT : 𝔛) (hLT : L ≤ T) :
     ∫ z, separatedMatrixCost 𝔐 z ∂𝔅 ≤
      𝘕₁ * (1024 * |lam| * 𝙷₁) ^ 𝔗 * 𝖫₁ * 𝔔 := by
  have hm : Measurable 𝔇 :=
    𝔊
  rw [cardinal_band_integral_eq_copies L T _ hm
    (by simpa only [cardinal_band_cost_eq] using cardinal_separated_cost_integrable lam hT)
    $ by simpa only [cardinal_band_cost_eq] using cardinal_separated_cost_integrable lam 𝔉 ]
  simp_rw [cardinal_band_cost_eq]
  have hsmall : n * (1024 * |lam| * 𝙷₁) ^ 𝔗 * 𝔒 ^ 2 *
      (1 + Real.log 𝔒) ^ 𝔡 ≤
      n * (1024 * |lam| * 𝙷₁) ^ 𝔗 * 𝖫₁ * 𝔔 := by
    bound
  have h := add_le_add (cardinal_separated_cost_integral_le (d := d) (D := D) hn lam hT)
    $ (𝔦 cardinal_separated_cost_integral_le hn lam 𝔉).trans hsmall
  linarith

𝗇 𝔓 𝙇
𝗇 𝔚 cardinalSeparatedSymmetricFactor lam z U
theorem cardinal_separated_symmetric_factor_measurable lam (U : 𝔓) :
    Measurable 𝔣 𝔚 := (Finset.measurable_fun_sum _ fun τ _ => Finset.measurable_fun_prod _
     fun l _ => cardinal_separated_factor_measurable lam l $ U $ τ l ).div_const _

𝗇 𝔑 cardinalSeparatedSymmetricFactor lam z.2 U * cardinalBandAmplitude lam z β β'
𝗃 𝔢 integratedCardinalMatrix lam ἀ U β β'
𝗃 𝔤 fun z => 𝔚 * cardinalBandAmplitude lam ἀ β β'
/-- Actual positive representation of E_T minus E_(max(1,L)), with
symmetric marks and the true permutation-averaged packet factors. -/
theorem integrated_cardinal_band_separated_exact lam (hlam : 𝖺)
    L (hT : 𝔛) (U : 𝔓) (hU : ∀ l r, |𝚚₂| ≤ 2)
    (β β' : 𝔖) :
    𝔢 T - 𝔢 𝔒 =
      ∫ z, 𝔑
        ∂𝔅 := by
  have hm : Measurable 𝔣 𝔑 :=
    ((cardinal_separated_symmetric_factor_measurable lam U).comp measurable_snd).mul
      $ cardinal_band_amplitude_measurable lam β β'
  have hiT : Integrable 𝔤 𝔍 𝔎 := by
    simpa only [cardinalBandAmplitude, Bool.false_eq_true, ite_false] using
      cardinal_separated_symmetric_entry_integrable lam hT U hU β β'
  have hiL : Integrable 𝔤 𝔏 𝔄 := by
    have hh := (cardinal_separated_symmetric_entry_integrable lam 𝔉 U hU β β').neg
    change Integrable (fun z => -(𝔚 *
      cardinalSeparatedAmplitude lam z β β')) 𝔄 at hh
    simpa only [cardinalBandAmplitude, ite_true, mul_neg] using hh
  rw [cardinal_band_integral_eq_copies L T _ hm hiT hiL]
  simp only [cardinalBandAmplitude, Bool.false_eq_true, ite_false, ite_true, mul_neg, integral_neg]
  rw [← integrated_cardinal_symmetric_separated_exact lam hlam hT U hU β β',
    ← integrated_cardinal_symmetric_separated_exact lam hlam 𝔉 U hU β β']
  ring

𝗇 𝔠 0 < L
theorem spatial_scale_domain_empty_below_one (i : Fin n)
    (hL : 𝔠) (hL1 : L < 1) : spatialScaleDomain i L = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have hnn : 0 ≤ 𝚞₂ := by
    apply Finset.sum_nonneg
    bound
  have hl := Real.log_neg hL hL1
  have hc : 𝚞₂ ≤ 2 * Real.log L := ht.2
  linarith

𝗇 𝔘 𝔢 L
theorem integrated_cardinal_matrix_below_one_eq_zero
    (i : Fin n) lam (hL : 𝔠) (hL1 : L < 1)
    (U : 𝔓) (β β' : 𝔖) :
    𝔘 = 0 := by
  unfold integratedCardinalMatrix spatialScaleMeasure
  simp_rw [spatial_scale_domain_empty_below_one _ hL hL1, Measure.restrict_empty, integral_zero_measure]
  exact Finset.sum_const_zero

theorem integrated_cardinal_matrix_max_one (hn : 𝗏)
    lam (hL : 𝔠) (U : 𝔓) (β β' : 𝔖) :
    𝔢 𝔒 = 𝔘 := by
  by_cases hL1 : 𝚛₂
  · simp_all
  · rw [max_eq_left (not_le.mp hL1).le, integrated_cardinal_matrix_one_eq_zero hn,
      integrated_cardinal_matrix_below_one_eq_zero ⟨0, 𝖡₃ ⟩ lam hL $ not_le.mp hL1 ]
    rfl

/-- Positive separated representation of every actual band with 0<L≤T,
including the zero convention below scale one. -/
theorem integrated_cardinal_actual_band_separated_exact (hn : 𝗏)
    lam (hlam : 𝖺) (hL : 𝔠) (hT : 𝔛)
    U (hU : ∀ l r, |𝚚₂| ≤ 2) (β β' : 𝔖) :
    𝔢 T - 𝔘 =
      ∫ z, 𝔑
        ∂𝔅 := by
  rw [← integrated_cardinal_matrix_max_one hn lam hL U β β']
  exact integrated_cardinal_band_separated_exact lam hlam L hT U hU β β'
