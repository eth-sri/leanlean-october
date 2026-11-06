module

public import NearlyMinimax.Risk


@[expose] public section

/-! Integrated risk of the actual floored and clipped ratio statistic.
The denominator mean is used only through its proved scalar lower bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false


variable {lo hi V ED a : ℝ}
theorem stabilized_ratio_sq_error {lo hi V N D ED a : ℝ}
    (ha : 0 < a) (hlo : lo ≤ V) (hhi : V ≤ hi)
    (hV : 0 ≤ V) (hED : 2 * a ≤ ED) :
    (clip lo hi (N / max D a) - V) ^ 2 ≤
      (2 / a ^ 2) * ((N - V * D) ^ 2 + hi ^ 2 * (D - ED) ^ 2) := by
  have hmax  := ha.trans_le (le_max_right D a)
  have  := hV.trans hhi
  have h_denominator_floor_error : |max D a - D| ≤ |D - ED| := by
    by_cases hDa : a ≤ D
    · simp [max_eq_left hDa]
    · have hDa'  := le_of_lt (lt_of_not_ge hDa)
      rw [max_eq_right hDa', abs_of_nonneg (sub_nonneg.mpr hDa'),
        abs_of_nonpos (sub_nonpos.mpr (hDa'.trans (by linarith)))]
      linarith
  have := h_denominator_floor_error
  have hnum : |N - V * max D a| ≤ |N - V * D| + hi * |D - ED| := by
    calc
      |N - V * max D a| = |(N - V * D) - V * (max D a - D)| := by congr 1; ring
      _ ≤ |N - V * D| + |V * (max D a - D)| := abs_sub _ _
      _ = |N - V * D| + V * |max D a - D| := by rw [abs_mul, abs_of_nonneg hV]
      _ ≤ |N - V * D| + hi * |D - ED| := by
        gcongr
  have hmain : |N / max D a - V| ≤
      a⁻¹ * (|N - V * D| + hi * |D - ED|) := by
    have hid : N / max D a - V = (N - V * max D a) / max D a := by
      field_simp
    rw [hid, abs_div, abs_of_pos hmax]
    have htotal : 0 ≤ |N - V * D| + hi * |D - ED| := by positivity
    calc
      |N - V * max D a| / max D a ≤
          (|N - V * D| + hi * |D - ED|) / max D a := by
        exact div_le_div_of_nonneg_right hnum hmax.le
      _ ≤ (|N - V * D| + hi * |D - ED|) / a :=
        div_le_div_of_nonneg_left htotal ha (le_max_right D a)
      _ = _ := by ring
  have hs := pow_le_pow_left₀ (abs_nonneg _) ((clip_error_le hlo hhi).trans hmain) 2
  rw [sq_abs] at hs
  calc
    _ ≤ (a⁻¹ * (|N - V * D| + hi * |D - ED|)) ^ 2 := hs
    _ = (a⁻¹) ^ 2 * (|N - V * D| + hi * |D - ED|) ^ 2 := by ring
    _ ≤ (a⁻¹) ^ 2 * (2 * (|N - V * D| ^ 2 + (hi * |D - ED|) ^ 2)) :=
      mul_le_mul_of_nonneg_left add_sq_le (sq_nonneg _)
    _ = _ := by rw [sq_abs, mul_pow, sq_abs]; ring

def stabilizedRatio  (lo hi a : ℝ) (N D : Ω → ℝ) (x : Ω) : ℝ :=
  clip lo hi (N x / max (D x) a)

theorem stabilizedRatio_measurable  [MeasurableSpace Ω]
    (lo hi a ) {N D : Ω → ℝ} (hN : Measurable N) (hD : Measurable D) :
    Measurable (stabilizedRatio lo hi a N D) :=
  (clip_lipschitz lo hi).continuous.measurable.comp
    (hN.div (hD.max measurable_const))

theorem stabilizedRatio_error_memLp  [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]  {N D : Ω → ℝ}
    (hN : Measurable N) (hD : Measurable D) (hlo : lo ≤ V) (hhi : V ≤ hi) :
    MemLp (fun x => stabilizedRatio lo hi a N D x - V) 2 μ := by
  have hm : Measurable (fun x => stabilizedRatio lo hi a N D x - V) :=
    (stabilizedRatio_measurable lo hi a hN hD).sub measurable_const
  apply MemLp.of_bound hm.aestronglyMeasurable (hi - lo)
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, stabilizedRatio] using clip_error_le_diameter hlo hhi
    (x := N x / max (D x) a)

/-- The reusable Bochner MSE inequality for the actual stabilized ratio. -/
theorem stabilized_ratio_mse_le  [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]  {N D : Ω → ℝ}
    (hN : Measurable N) (hD : Measurable D)
    (hS : MemLp (fun x => N x - V * D x) 2 μ) (hD2 : MemLp D 2 μ)
    (ha : 0 < a) (hlo : lo ≤ V) (hhi : V ≤ hi)
    (hV : 0 ≤ V) (hED : 2 * a ≤ ED) :
    (∫ x, (stabilizedRatio lo hi a N D x - V) ^ 2 ∂μ) ≤
      (2 / a ^ 2) * ((∫ x, (N x - V * D x) ^ 2 ∂μ) +
        hi ^ 2 * (∫ x, (D x - ED) ^ 2 ∂μ)) := by
  have hDc : MemLp (fun x => D x - ED) 2 μ := hD2.sub (memLp_const ED)
  have hiR : Integrable (fun x => (2 / a ^ 2) *
      ((N x - V * D x) ^ 2 + hi ^ 2 * (D x - ED) ^ 2)) μ :=
    (hS.integrable_sq.add (hDc.integrable_sq.const_mul _)).const_mul _
  have hb := integral_mono ((stabilizedRatio_error_memLp μ (a := a) hN hD hlo hhi).integrable_sq) hiR
    (fun x => stabilized_ratio_sq_error ha hlo hhi hV hED (N := N x) (D := D x))
  rw [integral_const_mul,
    integral_add (f := fun x => (N x - V * D x) ^ 2)
      (g := fun x => hi ^ 2 * (D x - ED) ^ 2)
      hS.integrable_sq (hDc.integrable_sq.const_mul _), integral_const_mul] at hb
  exact hb

/-- The same inequality in extended-valued risk, without replacing a
nonintegrable loss by the default Bochner integral. -/
theorem stabilized_ratio_lintegral_mse_le  [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]  {N D : Ω → ℝ}
    (hN : Measurable N) (hD : Measurable D)
    (hS : MemLp (fun x => N x - V * D x) 2 μ) (hD2 : MemLp D 2 μ)
    (ha : 0 < a) (hlo : lo ≤ V) (hhi : V ≤ hi)
    (hV : 0 ≤ V) (hED : 2 * a ≤ ED) :
    (∫⁻ x, ENNReal.ofReal ((stabilizedRatio lo hi a N D x - V) ^ 2) ∂μ) ≤
      ENNReal.ofReal ((2 / a ^ 2) * ((∫ x, (N x - V * D x) ^ 2 ∂μ) +
        hi ^ 2 * (∫ x, (D x - ED) ^ 2 ∂μ))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (stabilizedRatio_error_memLp μ (a := a) hN hD hlo hhi).integrable_sq
    (Eventually.of_forall (fun x => sq_nonneg _))]
  exact ENNReal.ofReal_mono (stabilized_ratio_mse_le μ hN hD hS hD2 ha hlo hhi hV hED)

end NearlyMinimax
