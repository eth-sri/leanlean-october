module

public import Mathlib

@[expose] public section

/-!
# Asymptotics of the actual upper saddle parameters

This module proves the square-root and logarithmic expansions used for the
candidate upper allocation. All assertions concern explicit scalar sequences;
they do not assert statistical admissibility or an estimator risk bound.
-/

noncomputable section
open Filter
open scoped Topology

namespace NearlyMinimax

/-- The width `S=a_* sqrt(log n)-C_S`. -/
def allocationWidth (a C x : ℝ) : ℝ := a * Real.sqrt (Real.log x) - C

/-- The candidate terminal depth `T°`, before dyadic flooring. -/
def candidateTerminalDepth (a C H γ x : ℝ) : ℝ :=
  allocationWidth a C x - Real.log (H * allocationWidth a C x) - γ * Real.log (allocationWidth a C x)

theorem tendsto_sqrt_log_atTop :
    Tendsto (fun x => Real.sqrt (Real.log x)) atTop atTop := by
  simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop

/-- Taking logarithms of a positive asymptotic multiple of `sqrt (log x)`
gives the additive residual, both for continuous and for rounded scales. -/
theorem log_sqrt_log_residual {f : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hf : Tendsto f atTop atTop)
    (hr : Tendsto (fun x => f x / Real.sqrt (Real.log x)) atTop (𝓝 a)) :
    Tendsto (fun x => Real.log (f x) - Real.log (Real.log x) / 2) atTop (𝓝 (Real.log a)) := by
  apply ((Real.continuousAt_log ha.ne').tendsto.comp hr).congr'
  filter_upwards [eventually_gt_atTop 1, hf.eventually (eventually_gt_atTop 0)] with x hx hfx
  simp [Function.comp_apply, Real.log_div hfx.ne' (Real.sqrt_pos.2 (Real.log_pos hx)).ne', Real.log_sqrt (Real.log_pos hx).le]

section
variable {a H δ L T β : ℝ} (ha : 0 < a) (hH : 0 < H) (hβ : 0 < β) (p C : ℝ) (q : ℕ) (γ : ℝ) (hδ : 0 < δ)
    (lam c : ℝ)

include ha in
theorem allocationWidth_tendsto_atTop :
    Tendsto (allocationWidth a C) atTop atTop := by
  have h := tendsto_atTop_add_const_right atTop (-C)
    (tendsto_sqrt_log_atTop.const_mul_atTop ha)
  assumption

theorem allocationWidth_div_sqrt_log_limit (a C : ℝ) :
    Tendsto (fun x => allocationWidth a C x / Real.sqrt (Real.log x)) atTop (𝓝 a) := by
  have hc : Tendsto (fun x => C / Real.sqrt (Real.log x)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_sqrt_log_atTop.inv_tendsto_atTop.const_mul C
  have h := (tendsto_const_nhds (x := a)).sub hc
  simp at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hp  := (Real.sqrt_pos.2 (Real.log_pos hx)).ne'
  unfold allocationWidth
  field_simp

include ha in
/-- The exact `O(1)` logarithmic correction has the limit `log a`. -/
theorem log_allocationWidth_residual_limit :
    Tendsto (fun x => Real.log (allocationWidth a C x) - Real.log (Real.log x) / 2)
      atTop (𝓝 (Real.log a)) :=
  log_sqrt_log_residual ha (allocationWidth_tendsto_atTop ha C) (allocationWidth_div_sqrt_log_limit a C)

include ha hH in
/-- The logarithmic correction in `T°` is proved, including its constant limit. -/
theorem terminalDepth_expansion_limit :
    Tendsto (fun x => candidateTerminalDepth a C H γ x - a * Real.sqrt (Real.log x) +
      (1 + γ) / 2 * Real.log (Real.log x)) atTop
        (𝓝 (-C - Real.log H - (1 + γ) * Real.log a)) := by
  have hl := log_allocationWidth_residual_limit ha C
  have h := ((tendsto_const_nhds (x := -C - Real.log H)).sub (hl.const_mul (1 + γ)))
  refine h.congr' ?_
  filter_upwards [(allocationWidth_tendsto_atTop ha C).eventually
    (eventually_gt_atTop 0)] with x hw
  unfold candidateTerminalDepth allocationWidth
  unfold allocationWidth at hw
  rw [Real.log_mul hH.ne' hw.ne']
  ring

include ha hH in
/-- The logarithmic depth correction is negligible relative to the diverging width. -/
theorem terminalDepth_div_width_limit :
    Tendsto (fun x => candidateTerminalDepth a C H γ x / allocationWidth a C x)
      atTop (𝓝 1) := by
  have hw := allocationWidth_tendsto_atTop ha C
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hw
  have hc : Tendsto (fun x => Real.log H / allocationWidth a C x) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hw.inv_tendsto_atTop.const_mul (Real.log H)
  have ht := ((tendsto_const_nhds (x := 1)).sub (hl.const_mul (1 + γ))).sub hc
  simp only [mul_zero, sub_zero] at ht
  refine ht.congr' ?_
  filter_upwards [hw.eventually (eventually_gt_atTop 0)] with x hx
  simp
  unfold candidateTerminalDepth
  rw [Real.log_mul hH.ne' hx.ne']
  field_simp
  ring

include ha hH in
theorem candidateTerminalDepth_tendsto_atTop :
    Tendsto (candidateTerminalDepth a C H γ) atTop atTop := by
  have hw := allocationWidth_tendsto_atTop ha C
  have hm := hw.atTop_mul_pos zero_lt_one (terminalDepth_div_width_limit ha hH C γ)
  refine hm.congr' ?_
  filter_upwards [hw.eventually (eventually_gt_atTop 0)] with x hx
  exact mul_div_cancel₀ _ hx.ne'

include ha hH in
/-- The unrounded saddle risk scale has an exact positive ratio limit. -/
theorem upper_saddle_scale_ratio_limit :
    Tendsto (fun x =>
      Real.exp (-lam * Real.log x - c * candidateTerminalDepth a C H γ x) /
        Real.exp (-lam * Real.log x - c * a * Real.sqrt (Real.log x) +
          c * (1 + γ) / 2 * Real.log (Real.log x))) atTop
      (𝓝 (Real.exp (c * (C + Real.log H + (1 + γ) * Real.log a)))) := by
  have ht := (terminalDepth_expansion_limit ha hH C γ).const_mul (-c)
  have hl := Real.continuous_exp.continuousAt.tendsto.comp ht
  have hvalue : -c * (-C - Real.log H - (1 + γ) * Real.log a) =
      c * (C + Real.log H + (1 + γ) * Real.log a) := by ring
  rw [hvalue] at hl
  apply hl.congr'
  filter_upwards [] with x
  simp
  rw [← Real.exp_sub]
  ring

include ha hH in
/-- The unrounded allocation scale is therefore bounded above and below by the displayed rate. -/
theorem upper_saddle_scale_bracket :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ᶠ x in atTop,
      A * Real.exp (-lam * Real.log x - c * a * Real.sqrt (Real.log x) +
        c * (1 + γ) / 2 * Real.log (Real.log x)) ≤
          Real.exp (-lam * Real.log x - c * candidateTerminalDepth a C H γ x) ∧
      Real.exp (-lam * Real.log x - c * candidateTerminalDepth a C H γ x) ≤
        B * Real.exp (-lam * Real.log x - c * a * Real.sqrt (Real.log x) +
          c * (1 + γ) / 2 * Real.log (Real.log x)) := by
  let Q := Real.exp (c * (C + Real.log H + (1 + γ) * Real.log a))
  have hQ : 0 < Q := Real.exp_pos _
  have ht := upper_saddle_scale_ratio_limit ha hH C γ lam c
  refine ⟨Q / 2, 2 * Q, by positivity, by positivity, ?_⟩
  filter_upwards [ht.eventually (lt_mem_nhds (by linarith [hQ] : Q / 2 < Q)),
    ht.eventually (gt_mem_nhds (by linarith [hQ] : Q < 2 * Q))] with x hlo hhi
  have hp := Real.exp_pos (-lam * Real.log x - c * a * Real.sqrt (Real.log x) +
    c * (1 + γ) / 2 * Real.log (Real.log x))
  exact ⟨((lt_div_iff₀ hp).1 hlo).le, ((div_lt_iff₀ hp).1 hhi).le⟩

/-- Natural flooring of the terminal log-cell count. -/
def roundedTerminalDepth (δ L T : ℝ) : ℝ :=
  δ * (Nat.floor ((L + T) / δ)) - L

include hδ in
/-- The exact one-cell loss due to dyadic terminal-depth rounding. -/
theorem roundedTerminalDepth_bounds (hLT : 0 ≤ L + T) :
    T - δ < roundedTerminalDepth δ L T ∧ roundedTerminalDepth δ L T ≤ T := by
  have hu := Nat.floor_le (div_nonneg hLT hδ.le)
  have hl := Nat.lt_floor_add_one ((L + T) / δ)
  have hum := mul_le_mul_of_nonneg_left hu hδ.le
  have hlm := mul_lt_mul_of_pos_left hl hδ
  have he : δ * ((L + T) / δ) = L + T := by field_simp
  rw [he] at hum hlm
  unfold roundedTerminalDepth
  constructor <;> linarith

/-- Dyadic flooring changes the scalar risk scale by a bounded fixed factor. -/
theorem rounded_saddle_scale_bounds {c lam : ℝ}
    (hδ : 0 < δ) (hLT : 0 ≤ L + T) (hc : 0 ≤ c) :
    let expScale := Real.exp (-lam * L - c * roundedTerminalDepth δ L T)
    Real.exp (-lam * L - c * T) ≤ expScale ∧
      expScale ≤
        Real.exp (c * δ) * Real.exp (-lam * L - c * T) := by
  obtain ⟨hl, hu⟩ := roundedTerminalDepth_bounds hδ hLT
  constructor
  · apply Real.exp_le_exp.2
    bound
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith

include ha hH in
/-- The candidate terminal-cell count is eventually nonnegative. -/
theorem eventually_terminal_cell_log_nonneg :
    ∀ᶠ x in atTop, 0 ≤ Real.log x + candidateTerminalDepth a C H γ x := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop 0),
    (candidateTerminalDepth_tendsto_atTop ha hH C γ).eventually (eventually_ge_atTop 0)]
    with x hx ht
  positivity

include ha hH hδ in
/-- This is the full scalar saddle rate after dyadic terminal-depth rounding. -/
theorem rounded_upper_saddle_scale_bracket (C γ lam : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ᶠ x in atTop,
      A * Real.exp (-lam * Real.log x - c * a * Real.sqrt (Real.log x) +
        c * (1 + γ) / 2 * Real.log (Real.log x)) ≤
          Real.exp (-lam * Real.log x - c * roundedTerminalDepth δ (Real.log x) (candidateTerminalDepth a C H γ x)) ∧
      Real.exp (-lam * Real.log x - c * roundedTerminalDepth δ (Real.log x) (candidateTerminalDepth a C H γ x)) ≤
        B * Real.exp (-lam * Real.log x - c * a * Real.sqrt (Real.log x) +
          c * (1 + γ) / 2 * Real.log (Real.log x)) := by
  obtain ⟨A, B, hA, hB, hb⟩ := upper_saddle_scale_bracket ha hH C γ lam c
  refine ⟨A, Real.exp (c * δ) * B, hA, mul_pos (Real.exp_pos _) hB, ?_⟩
  filter_upwards [hb, eventually_terminal_cell_log_nonneg ha hH C γ] with x hx ht
  obtain ⟨hl, hu⟩ := rounded_saddle_scale_bounds hδ ht hc
  constructor
  · exact hx.1.trans hl
  · apply hu.trans
    have hm := mul_le_mul_of_nonneg_left hx.2 (Real.exp_pos (c * δ)).le
    simpa only [mul_assoc] using hm

include ha hβ in
/-- The lower profile-degree threshold is met eventually by the actual width. -/
theorem eventually_width_degree_threshold :
    ∀ᶠ x in atTop, q + 2 ≤ β * allocationWidth a C x / 4 := by
  have ht := (allocationWidth_tendsto_atTop ha C).const_mul_atTop
    (by positivity : 0 < β / 4)
  have he := ht.eventually (eventually_ge_atTop ((q : ℝ) + 2))
  filter_upwards [he] with x hx
  bound

/-- Every fixed power of the logarithm is negligible relative to the sample size. -/
theorem tendsto_log_power_div_sample :
    Tendsto (fun x => (Real.log x) ^ p / x) atTop (𝓝 0) := by
  simpa using (isLittleO_log_rpow_rpow_atTop p (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero

end

/-- A concrete eventual version sufficient for sample-size guards on degree scales. -/
theorem eventually_log_power_lt_sample (p A : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x in atTop, A * (Real.log x) ^ p < δ * x := by
  have h := (tendsto_log_power_div_sample p).const_mul A
  simp at h
  filter_upwards [h.eventually (gt_mem_nhds hδ), eventually_gt_atTop 0] with x hx hx₀
  have hr : A * (Real.log x) ^ p / x < δ := by simpa only [mul_div_assoc] using hx
  exact (div_lt_iff₀ hx₀).1 hr

end NearlyMinimax
