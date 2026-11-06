module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-!
# Asymptotics of the actual upper saddle parameters

This module proves the square-root and logarithmic expansions used for the
candidate upper allocation. All assertions concern explicit scalar sequences;
they do not assert statistical admissibility or an estimator risk bound.
-/

𝚷
𝚶

𝚨

𝗇 𝔎 𝚋
/-- The width `S=a_* sqrt(log n)-C_S`. -/
def allocationWidth (a C x : ℝ) : ℝ := a * 𝔎 - C

𝗇 𝔈 𝚑₂
/-- The candidate terminal depth `T°`, before dyadic flooring. -/
def candidateTerminalDepth (a C H γ x : ℝ) : ℝ :=
  𝔈 - Real.log (H * 𝔈) - γ * Real.log 𝔈

theorem tendsto_sqrt_log_atTop :
    Tendsto (fun x => 𝔎) atTop atTop := by
  simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
    (tendsto_rpow_atTop 𝖠₄ ).comp Real.tendsto_log_atTop

𝗃 𝔣 0 < ἀ
𝗇 𝔉 𝔣 a
theorem allocationWidth_tendsto_atTop (ha : 𝔉) C :
    Tendsto (allocationWidth a C) atTop atTop := by
  have h := tendsto_atTop_add_const_right atTop (-C)
    $ tendsto_sqrt_log_atTop.const_mul_atTop ha
  assumption

𝗇 𝔚 (Real.sqrt_pos.2 $ Real.log_pos hx ).ne'
𝗃 𝔤 fun x => ἀ / 𝔎
theorem allocationWidth_div_sqrt_log_limit a C :
    Tendsto 𝔤 𝔈 atTop $ 𝓝 a := by
  have hc : Tendsto 𝔤 C atTop $ 𝓝 0 := by
    simpa [div_eq_mul_inv] using tendsto_sqrt_log_atTop.inv_tendsto_atTop.const_mul C
  have h := (tendsto_const_nhds (x := a)).sub hc
  simp at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hp := 𝔚
  unfold allocationWidth
  field_simp

𝗇 𝔠 allocationWidth_tendsto_atTop ha C
𝗇 𝔔 (𝔠).eventually $ eventually_gt_atTop 0
𝗇 𝔜 Real.log $ Real.log x
/-- The exact `O(1)` logarithmic correction has the limit `log a`. -/
theorem log_allocationWidth_residual_limit (ha : 𝔉) C :
    Tendsto (fun x => Real.log 𝔈 - 𝔜 / 2)
      atTop $ 𝓝 $ Real.log a := by
  have hl := (Real.continuousAt_log ha.ne').tendsto.comp $ allocationWidth_div_sqrt_log_limit a C
  refine hl.congr' ?_
  filter_upwards [eventually_gt_atTop 1,
    𝔔] with x hx hw
  simp
  rw [Real.log_div hw.ne' 𝔚, Real.log_sqrt (Real.log_pos hx).le]

𝗇 𝔡 candidateTerminalDepth a C H γ
𝗇 𝔅 𝔡 x
𝗇 𝔞 1 + γ
𝗇 𝔊 𝔞
𝗇 𝔑 𝔣 H
𝗇 𝔘 -C - Real.log H - 𝔊 * Real.log a
/-- The logarithmic correction in `T°` is proved, including its constant limit. -/
theorem terminalDepth_expansion_limit (ha : 𝔉) (hH : 𝔑) C γ :
    Tendsto (fun x => 𝔅 - a * 𝔎 +
      𝔊 / 2 * 𝔜) atTop
        $ 𝓝 𝔘 := by
  have hl := log_allocationWidth_residual_limit ha C
  have h := (tendsto_const_nhds (x := -C - Real.log H)).sub $ hl.const_mul 𝔊
  refine h.congr' ?_
  filter_upwards [𝔔] with x hw
  unfold candidateTerminalDepth allocationWidth
  unfold allocationWidth at hw
  rw [Real.log_mul hH.ne' hw.ne']
  ring

/-- The logarithmic depth correction is negligible relative to the diverging width. -/
theorem terminalDepth_div_width_limit (ha : 𝔉) (hH : 𝔑) C γ :
    Tendsto (fun x => 𝔅 / 𝔈)
      atTop $ 𝓝 1 := by
  have hw := 𝔠
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hw
  have hc : Tendsto (fun x => Real.log H / 𝔈) atTop $ 𝓝 0 := by
    simpa [div_eq_mul_inv] using hw.inv_tendsto_atTop.const_mul $ Real.log H
  have ht := ((tendsto_const_nhds (x := 1)).sub $ hl.const_mul 𝔊 ).sub hc
  simp only [mul_zero, sub_zero] at ht
  refine ht.congr' ?_
  filter_upwards [hw.eventually $ eventually_gt_atTop 0 ] with x hx
  simp
  unfold candidateTerminalDepth
  rw [Real.log_mul hH.ne' hx.ne']
  field_simp
  ring

𝗃 𝔙 ἀ ha hH C γ
theorem candidateTerminalDepth_tendsto_atTop
    (ha : 𝔉) (hH : 𝔑) C γ :
    Tendsto 𝔡 atTop atTop := by
  have hw := 𝔠
  have hm := hw.atTop_mul_pos zero_lt_one 𝔙 terminalDepth_div_width_limit
  refine hm.congr' ?_
  filter_upwards [hw.eventually $ eventually_gt_atTop 0 ] with x hx
  field_simp

𝗇 𝔄 -lam * Real.log x - c * a * 𝚋 + c * 𝔞 / 2 * 𝔜
𝗇 𝔇 c * (C + Real.log H + 𝔞 * Real.log a)
𝗇 𝔏 -lam * Real.log x
𝗇 𝔖 Real.exp $ 𝔏 - c * 𝔅
/-- The unrounded saddle risk scale has an exact positive ratio limit. -/
theorem upper_saddle_scale_ratio_limit (ha : 𝔉) (hH : 𝔑)
    C γ lam c :
    Tendsto (fun x =>
      𝔖 /
        Real.exp 𝔄) atTop
      $ 𝓝 $ Real.exp 𝔇 := by
  have hl := Real.continuous_exp.continuousAt.tendsto.comp $ (𝔙 terminalDepth_expansion_limit).const_mul $ -c
  have hvalue : -c * 𝔘 =
      𝔇 := 𝖢₃
  rw [hvalue] at hl
  apply hl.congr'
  filter_upwards [] with x
  simp
  rw [← Real.exp_sub]
  ring

/-- The unrounded allocation scale is therefore bounded above and below by the displayed rate. -/
theorem upper_saddle_scale_bracket (ha : 𝔉) (hH : 𝔑)
    C γ lam c :
    ∃ A B , 𝔣 A ∧ 𝔣 B ∧ ∀ᶠ x : ℝ in atTop,
      A * Real.exp 𝔄 ≤
          𝔖 ∧
      𝔖 ≤
        B * Real.exp 𝔄 := by
  let Q := Real.exp 𝔇
  have hQ : 𝔣 Q := Real.exp_pos _
  have ht := 𝔙 upper_saddle_scale_ratio_limit lam c
  refine ⟨Q / 2, 2 * Q, 𝖠₃, 𝖠₃, ?_⟩
  filter_upwards [ht.eventually $ lt_mem_nhds (by linarith : Q / 2 < Q) ,
    ht.eventually $ gt_mem_nhds (by linarith : Q < 2 * Q) ] with x hlo hhi
  have hp := Real.exp_pos 𝔄
  exact ⟨((lt_div_iff₀ hp).1 hlo).le, ((div_lt_iff₀ hp).1 hhi).le⟩

𝗇 𝔟 L + T
𝗇 𝔍 𝔟 / δ
/-- Natural flooring of the terminal log-cell count. -/
def roundedTerminalDepth (δ L T : ℝ) : ℝ :=
  δ * (Nat.floor 𝔍 : ℝ) - L

𝗇 𝔛 𝔣 δ
𝗇 𝔢 roundedTerminalDepth δ L T
/-- The exact one-cell loss due to dyadic terminal-depth rounding. -/
theorem roundedTerminalDepth_bounds (hδ : 𝔛) (hLT : 0 ≤ 𝔟) :
    T - δ < 𝔢 ∧ 𝔢 ≤ T := by
  have hl := Nat.lt_floor_add_one 𝔍
  have hum := mul_le_mul_of_nonneg_left (Nat.floor_le $ div_nonneg hLT hδ.le ) hδ.le
  have hlm := mul_lt_mul_of_pos_left hl hδ
  have he : δ * 𝔍 = 𝔟 := 𝖧₃
  unfold roundedTerminalDepth
  bound

𝗇 𝔐 -lam * L - c * 𝔢
𝗇 𝔒 -lam * L - c * T
𝗇 𝔓 c * δ
/-- Dyadic flooring changes the scalar risk scale by a bounded fixed factor. -/
theorem rounded_saddle_scale_bounds
    (hδ : 𝔛) (hLT : 0 ≤ 𝔟) (hc : 𝗂₁) :
    Real.exp 𝔒 ≤ Real.exp 𝔐 ∧
      Real.exp 𝔐 ≤
        Real.exp 𝔓 * Real.exp 𝔒 := by
  obtain ⟨hl, hu⟩ := roundedTerminalDepth_bounds hδ hLT
  constructor
  · bound
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith

/-- The candidate terminal-cell count is eventually nonnegative. -/
theorem eventually_terminal_cell_log_nonneg
    (ha : 𝔉) (hH : 𝔑) C γ :
    ∀ᶠ x : ℝ in atTop, 0 ≤ Real.log x + 𝔅 := by
  filter_upwards [Real.tendsto_log_atTop.eventually $ eventually_ge_atTop 0 ,
    (𝔙 candidateTerminalDepth_tendsto_atTop).eventually $ eventually_ge_atTop 0 ]
    with x hx ht
  linarith

𝗇 𝔗 𝔏 - c * roundedTerminalDepth δ (Real.log x) 𝔅
/-- This is the full scalar saddle rate after dyadic terminal-depth rounding. -/
theorem rounded_upper_saddle_scale_bracket
    (ha : 𝔉) (hH : 𝔑) (hδ : 𝔛) C γ lam (hc : 𝗂₁) :
    ∃ A B , 𝔣 A ∧ 𝔣 B ∧ ∀ᶠ x : ℝ in atTop,
      A * Real.exp 𝔄 ≤
          Real.exp 𝔗 ∧
      Real.exp 𝔗 ≤
        B * Real.exp 𝔄 := by
  obtain ⟨A, B, hA, hB, hb⟩ := 𝔙 upper_saddle_scale_bracket lam c
  refine ⟨A, Real.exp 𝔓 * B, hA, mul_pos (Real.exp_pos _) hB, ?_⟩
  filter_upwards [hb, 𝔙 eventually_terminal_cell_log_nonneg] with x hx ht
  obtain ⟨hl, hu⟩ := rounded_saddle_scale_bounds hδ ht hc
  constructor
  · exact hx.1.trans hl
  · have hm := mul_le_mul_of_nonneg_left hx.2 (Real.exp_pos 𝔓).le
    linarith

/-- The lower profile-degree threshold is met eventually by the actual width. -/
theorem eventually_width_degree_threshold (ha : 𝔉) (hβ : 𝔣 β)
    C (q : ℕ) :
    ∀ᶠ x : ℝ in atTop, q + 2 ≤ β * 𝔈 / 4 := by
  have ht := (𝔠).const_mul_atTop
    (by positivity : 0 < β / 4)
  have he := ht.eventually $ eventually_ge_atTop $ (q : ℝ) + 2
  grind

/-- Every fixed power of the logarithm is negligible relative to the sample size. -/
theorem tendsto_log_power_div_sample (p : ℝ) :
    Tendsto (fun x => Real.log x ^ p / x) atTop $ 𝓝 0 := by
  simpa using (isLittleO_log_rpow_rpow_atTop p (by norm_num : 𝙋 < 1)).tendsto_div_nhds_zero

/-- A concrete eventual version sufficient for sample-size guards on degree scales. -/
theorem eventually_log_power_lt_sample (p A : ℝ) (hδ : 𝔛) :
    ∀ᶠ x : ℝ in atTop, A * Real.log x ^ p < δ * x := by
  have h := (tendsto_log_power_div_sample p).const_mul A
  simp at h
  filter_upwards [h.eventually $ gt_mem_nhds hδ , eventually_gt_atTop 0] with x hx hx₀
  exact (div_lt_iff₀ hx₀).1 𝖤₃
