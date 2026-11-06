module

public import NearlyMinimax.Risk
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Integrated risk of the actual floored and clipped ratio statistic.
The denominator mean is used only through its proved scalar lower bound. -/
open MeasureTheory ProbabilityTheory Filter
𝚮
𝚨
𝚩

𝗇 𝔇 N - V * D
𝗃 𝔘 ἀ ^ 2
𝗇 𝔍 2 / 𝔘 a
𝗇 𝔐 2 * a ≤ ED
𝗇 𝔑 D - ED
𝗇 𝔒 a⁻¹
𝗇 𝔔 lo ≤ V
𝗇 𝔖 V ≤ hi
theorem stabilized_ratio_sq_error
    (ha : 𝙆) (hlo : 𝔔) (hhi : 𝔖)
    (hV : 0 ≤ V) (hED : 𝔐) :
    (clip lo hi (N / max D a) - V) ^ 2 ≤
      𝔍 * (𝔘 𝔇 + 𝔘 hi * 𝔘 𝔑) := by
  have hs := 𝗂 (stabilized_ratio_error ha hlo hhi hV hED (N := N) (D := D)) 2
  rw [sq_abs] at hs
  calc
    _ ≤ (𝔒 * (|𝔇| + hi * |𝔑|)) ^ 2 := hs
    _ = 𝔘 𝔒 * (|𝔇| + hi * |𝔑|) ^ 2 := 𝖢₃
    _ ≤ 𝔘 𝔒 * (2 * (|𝔇| ^ 2 + (hi * |𝔑|) ^ 2)) :=
      mul_le_mul_of_nonneg_left add_sq_le $ sq_nonneg _
    𝘿 := 𝖤₃

def stabilizedRatio (lo hi a : ℝ) (N D : 𝘄) (x : Ω) : ℝ :=
  clip lo hi $ N x / max (D x) a

𝗇 𝔗 stabilizedRatio lo hi a N D
theorem stabilizedRatio_measurable {Ω } [MeasurableSpace Ω]
    lo hi a {N D : 𝘄} (hN : Measurable N) (hD : Measurable D) :
    Measurable 𝔗 :=
  (clip_lipschitz lo hi).continuous.measurable.comp
    $ hN.div $ hD.max measurable_const

𝗇 𝔅 𝔗 x - V
𝗃 𝔙 fun x => ἀ
𝗇 𝔓 𝔙 𝔅
theorem stabilizedRatio_error_memLp {Ω } [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {lo hi a V } {N D }
    (hN : Measurable N) (hD : Measurable D) (hlo : 𝔔) (hhi : 𝔖) :
    MemLp 𝔓 2 μ := by
  have hm : Measurable 𝔓 :=
    (stabilizedRatio_measurable lo hi a hN hD).sub measurable_const
  apply MemLp.of_bound hm.aestronglyMeasurable $ hi - lo
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, stabilizedRatio] using clip_error_le_diameter hlo hhi


𝗇 𝔊 N x - V * D x
𝗇 𝔎 D x - ED
𝗃 𝔏 ∫ x, 𝔘 ἀ ∂μ
𝗇 𝔄 𝔍 * (𝔏 𝔊 + 𝔘 hi * 𝔏 𝔎)
𝗇 𝔈 MemLp 𝔙 𝔊 2 μ
𝗇 𝔉 (stabilizedRatio_error_memLp μ hN hD hlo hhi).integrable_sq
/-- The reusable Bochner MSE inequality for the actual stabilized ratio. -/
theorem stabilized_ratio_mse_le [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hN : Measurable N) (hD : Measurable D)
    (hS : 𝔈) (hD2 : MemLp D 2 μ)
    (ha : 𝙆) (hlo : 𝔔) (hhi : 𝔖)
    (hV : 0 ≤ V) (hED : 𝔐) :
    𝔏 𝔅 ≤
      𝔄 := by
  have hDc : MemLp 𝔙 𝔎 2 μ := hD2.sub $ memLp_const ED
  have hiR : Integrable (fun x => 𝔍 *
      (𝔘 𝔊 + 𝔘 hi * 𝔘 𝔎)) μ :=
    (hS.integrable_sq.add $ hDc.integrable_sq.const_mul _ ).const_mul _
  have hb := integral_mono 𝔉 hiR
     fun x => stabilized_ratio_sq_error ha hlo hhi hV hED
  rw [integral_const_mul,
    integral_add

      hS.integrable_sq $ hDc.integrable_sq.const_mul _ , integral_const_mul] at hb
  exact hb

/-- The same inequality in extended-valued risk, without replacing a
nonintegrable loss by the default Bochner integral. -/
theorem stabilized_ratio_lintegral_mse_le [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hN : Measurable N) (hD : Measurable D)
    (hS : 𝔈) (hD2 : MemLp D 2 μ)
    (ha : 𝙆) (hlo : 𝔔) (hhi : 𝔖)
    (hV : 0 ≤ V) (hED : 𝔐) :
     ∫⁻ x, ENNReal.ofReal 𝔘 𝔅 ∂μ ≤
      ENNReal.ofReal 𝔄 := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    𝔉
    $ Eventually.of_forall fun x => sq_nonneg _ ]
  exact ENNReal.ofReal_mono $ stabilized_ratio_mse_le μ hN hD hS hD2 ha hlo hhi hV hED
