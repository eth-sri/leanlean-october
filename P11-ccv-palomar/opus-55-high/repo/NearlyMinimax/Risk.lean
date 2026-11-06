module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation

@[expose] public section

/-!
# Deterministic stabilization and score-to-risk comparison

This module formalizes the clipping and denominator-stabilization step
(eq. U14-stab), the fundamental-calculus part of Lemma path-risk, and
its finite-outcome probability specialization. The path theorem uses an
integrable derivative on the interval; it does not claim the paper's
full absolutely-continuous, almost-everywhere formulation.
-/

𝚸

𝚨


𝗇 𝔚 max lo $ min hi x
/-- Projection of a real-valued statistic to an interval. -/
def clip (lo hi x : ℝ) : ℝ := 𝔚

𝗇 𝔗 clip lo hi
𝗃 𝔣 fun x => ἀ
/-- Projection to the interval is `1`-Lipschitz. -/
theorem clip_lipschitz lo hi : LipschitzWith 1 𝔗 := by
  change LipschitzWith 1 𝔣 𝔚
  simpa only [id_eq] using (LipschitzWith.id.const_min hi).const_max lo

/-- The clipped statistic lies in the designated interval. -/
theorem clip_mem_Icc (hinterval : lo ≤ hi) :
    𝔗 x ∈ Icc lo hi := ⟨le_max_left .., max_le hinterval $ min_le_left .. ⟩

𝗇 𝔛 lo ≤ V
𝗇 𝔜 V ≤ hi
/-- Any clipped statistic and interval-valued target are separated by
at most the diameter of the interval. -/
theorem clip_error_le_diameter (hlo : 𝔛) (hhi : 𝔜) :
    |𝔗 x - V| ≤ hi - lo := by
  have hc := clip_mem_Icc (x := x) $ hlo.trans hhi
  grind

/-- Clipping fixes any target in the clipping interval. -/
theorem clip_target (hlo : 𝔛) (hhi : 𝔜) :
    𝔗 V = V := by
  simp [clip, min_eq_right hhi, max_eq_right hlo]

/-- Clipping cannot increase the absolute error at an admissible target. -/
theorem clip_error_le (hlo : 𝔛) (hhi : 𝔜) :
    |𝔗 x - V| ≤ |x - V| := by
  by_cases hxlo : x ≤ lo
  · rw [clip, min_eq_right $ hxlo.trans $ hlo.trans hhi , max_eq_left hxlo,
      abs_of_nonpos $ sub_nonpos.mpr hlo , abs_of_nonpos $ sub_nonpos.mpr $ hxlo.trans hlo ]
    linarith
  · by_cases hxhi : x ≤ hi
    · simp [clip, min_eq_right hxhi, max_eq_right $ le_of_lt $ lt_of_not_ge hxlo ]
    · have hhix := le_of_lt $ lt_of_not_ge hxhi
      rw [clip, min_eq_left hhix, max_eq_right $ hlo.trans hhi ,
        abs_of_nonneg $ sub_nonneg.mpr hhi ,
        abs_of_nonneg $ sub_nonneg.mpr $ hhi.trans hhix ]
      linarith

𝗇 𝔇 max D a
𝗇 𝔍 D - ED
𝗇 𝔔 𝔇 - D
/-- A denominator floored at `a` can move only as much as its discrepancy
from a reference mean greater than `a`. -/
theorem denominator_floor_error {a D ED : ℝ} (hED : a ≤ ED) :
    |𝔔| ≤ |𝔍| := by
  grind

𝗇 𝔄 N - V * D
𝗇 𝔓 N - V * 𝔇
𝗇 𝔞 N / 𝔇
𝗇 𝔟 le_max_right D a
/-- The stabilized and clipped pair-ratio inequality (eq. U14-stab).
`ED` represents the expected denominator. -/
theorem stabilized_ratio_error {lo hi V N D ED a }
    (ha : 𝙆) (hlo : 𝔛) (hhi : 𝔜)
    (hV : 0 ≤ V) (hED : 2 * a ≤ ED) :
    |𝔗 𝔞 - V| ≤
      a⁻¹ * (|𝔄| + hi * |𝔍|) := by
  have href : a ≤ ED := 𝖡₄
  have hhineg := hV.trans hhi
  have hf := denominator_floor_error (D := D) href
  have hnum : |𝔓| ≤ |𝔄| + hi * |𝔍| := by
    calc
      |𝔓| = |𝔄 - V * 𝔔| := 𝖢₃
      _ ≤ |𝔄| + |V * 𝔔| := abs_sub ..
      _ = |𝔄| + V * |𝔔| := 𝖤₄
      _ ≤ |𝔄| + hi * |𝔍| := by
        gcongr
  have hmain : |𝔞 - V| ≤
      a⁻¹ * (|𝔄| + hi * |𝔍|) := by
    have hid : 𝔞 - V = 𝔓 / 𝔇 := by
      field_simp
    rw [hid, abs_div, abs_of_pos $ ha.trans_le 𝔟 ]
    calc
      |𝔓| / 𝔇 ≤
          (|𝔄| + hi * |𝔍|) / 𝔇 := by
        bound
      _ ≤ (|𝔄| + hi * |𝔍|) / a :=
        div_le_div_of_nonneg_left  𝖠₃  ha 𝔟
      𝘿 := 𝖢₃
  exact (clip_error_le hlo hhi).trans hmain

𝗇 𝔊 ∀ t ∈ Icc 0 δ, HasDerivAt m (m' t) t
𝗇 𝔐 ∫ t in (0)..δ, scoreNorm t
𝗃 𝔡 IntervalIntegrable ἀ volume 0 δ
/-- The actual analytic integration step: a derivative bounded by
`r * scoreNorm` bounds the endpoint change by the integrated score norm. -/
theorem path_mean_change_le {m m' scoreNorm } {δ r : ℝ}
    (hδ : 𝚈)
    (hderiv : 𝔊)
    (hm' : 𝔡 m')
    (hscore : 𝔡 scoreNorm)
    (hbound : ∀ t ∈ Icc 0 δ, |m' t| ≤ r * scoreNorm t) :
    |m δ - m 0| ≤ r * 𝔐 := by
  have hFTC : ∫ t in 0..δ, m' t = m δ - m 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
       𝖤₄  hm'
  rw [← hFTC, ← intervalIntegral.integral_const_mul]
  simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_of_norm_le (f := m') hδ
    (Filter.Eventually.of_forall fun t ht => by
      simpa [Real.norm_eq_abs] using hbound t ⟨le_of_lt ht.1, ht.2⟩ )
    $ hscore.const_mul r

/-- Two endpoint errors and the integrated derivative bound imply the
linear score-to-risk bound of Lemma path-risk. -/
theorem path_separation_le {m m' scoreNorm } {δ r V₀ Vδ : ℝ}
    (hδ : 𝚈)
    (hderiv : 𝔊)
    (hm' : 𝔡 m')
    (hscore : 𝔡 scoreNorm)
    (hbound : ∀ t ∈ Icc 0 δ, |m' t| ≤ r * scoreNorm t)
    (hfirst : |m 0 - V₀| ≤ r) (hlast : |m δ - Vδ| ≤ r) :
    |Vδ - V₀| ≤ (2 + 𝔐) * r := by
  have hchange := path_mean_change_le hδ hderiv hm' hscore hbound
  grind

𝗇 𝔉 2 + B
𝗃 𝔤 ἀ ^ 2
𝗇 𝔠 𝔤 Δ / 𝔤 𝔉
/-- Squaring the comparison and subtracting the exceptional-state
contribution yields the risk lower bound in eq. path-risk. -/
theorem path_risk_lower_bound {Δ B r risk D ε : ℝ}
    (hB : 𝙐) (hr : 𝘵₁) (hΔ : 0 ≤ Δ)
    (hsep : Δ ≤ 𝔉 * r)
    (hrisk : 𝔤 r = risk + 𝔤 D * ε) :
    𝔠 - 𝔤 D * ε ≤ risk := by
  have hsq : 𝔤 Δ ≤ (𝔉 * r) ^ 2 := by
    bound
  have hdiv : 𝔠 ≤ 𝔤 r := by
    apply (div_le_iff₀ $ sq_pos_of_pos 𝖡₄ ).mpr
    linarith
  linarith

𝗃 𝔘 Real.sqrt $ ∫ x, ἀ x ^ 2 ∂μ
𝗇 𝔅 𝔘 f * 𝔘 g
𝗇 𝔎 f x * g x
𝗃 𝔥 MemLp ἀ 2 μ
/-- Integral Cauchy–Schwarz on an arbitrary measure space, stated with
ordinary real second moments. -/
theorem integral_cauchy_schwarz [MeasurableSpace α]
    (μ : Measure α) f g (hf : 𝔥 f) (hg : 𝔥 g) :
    |∫ x, 𝔎 ∂μ| ≤
      𝔅 := by
  have hholder : Real.HolderConjugate 2 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hcs := integral_mul_norm_le_Lp_mul_Lq hholder
    (by simpa using hf) $ by simpa using hg
  have hcs' : ∫ x, |f x| * |g x| ∂μ ≤
      𝔅 := by
    simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] using hcs
  calc
    |∫ x, 𝔎 ∂μ| ≤ ∫ x, |𝔎| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm 𝔣 𝔎
    _ = ∫ x, |f x| * |g x| ∂μ := 𝖢₄
    𝖦 := hcs'

𝗇 𝔖 T x - V
𝗇 𝔈 ∫ x, 𝔤 𝔖 ∂μ ≤ 𝔤 r
𝗇 𝔏 𝔣 𝔖
𝗇 𝔑 Real.sqrt_le_iff.mpr ⟨hr, hrisk⟩
𝗇 𝔙 hT.sub $ memLp_const V
𝗃 𝔢 ∫ x, ἀ x ∂μ
/-- Mean-square risk controls bias for arbitrary probability laws. -/
theorem probability_mean_error_le [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] T (V r : ℝ)
    (hT : 𝔥 T) (hr : 𝘵₁)
    (hrisk : 𝔈) :
    |𝔢 T - V| ≤ r := by
  have hcs := integral_cauchy_schwarz μ 𝔏 𝙃 𝔙 $ memLp_const 1
  have hTInt := hT.integrable 𝖠₄
  simp at hcs
  rw [integral_sub hTInt $ integrable_const V ] at hcs
  simp at hcs
  exact hcs.trans 𝔑

𝗇 𝔒 ∫ x, T x * R x ∂μ
/-- Centering and integral Cauchy–Schwarz prove the score derivative
bound on arbitrary probability spaces. -/
theorem probability_score_bound [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] T R V r
    (hT : 𝔥 T) (hR : 𝔥 R) (hr : 𝘵₁)
    (hcenter : 𝔢 R = 0)
    (hrisk : 𝔈) :
    |𝔒| ≤ r * 𝔘 R := by
  have hTRInt : Integrable (fun x => T x * R x) μ := hT.integrable_mul hR
  have hid : ∫ x, 𝔖 * R x ∂μ = 𝔒 := by
    simp_rw [sub_mul]
    rw [integral_sub hTRInt $ (hR.const_mul V).integrable 𝖠₄ , integral_const_mul, hcenter, mul_zero, sub_zero]
  have hcs := integral_cauchy_schwarz μ 𝔏 R
    𝔙 hR
  rw [hid] at hcs
  exact hcs.trans $ mul_le_mul_of_nonneg_right
    𝔑 $ Real.sqrt_nonneg _
