module

public import NearlyMinimax.Allocation
public import NearlyMinimax.SaddleAsymptotics
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-!
# Uniform scalar bounds for the floored allocation degrees

These lemmas prove the `O(log(n)^(3/2))` maximum-degree bound in the upper
allocation, from the explicit width and the actual scalar level-range bounds.
The ensuing sample-size comparison is uniform in the number of levels.
-/

𝚷
𝚶

𝚨

𝗇 𝔍 L * Real.sqrt L
𝗇 𝔖 𝖱₂ / Real.sqrt L
𝗃 𝔚 0 < ἀ
theorem sq_div_sqrt_eq_mul_sqrt (hL : 𝔚 L) :
    𝔖 = 𝔍 := by
  grind

𝗇 𝔈 (𝗞 : ℝ)
𝗇 𝔑 𝙖
theorem mul_sqrt_eq_three_halves_power (hL : 𝔚 L) :
    𝔍 = L ^ 𝔈 := by
  calc
    𝔍 = L ^ 1 * L ^ 𝔑 := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
    _ = L ^ (1 + 𝔑) := (Real.rpow_add hL 1 𝔑).symm
    _ = L ^ 𝔈 := 𝖠₄

𝗇 𝔙 C + 1
𝗇 𝔇 𝔙 ^ 2 / c
𝗇 𝔎 c * Real.sqrt L
𝗇 𝔒 𝔙 * L
𝗇 𝔗 (S - z) ^ 2
/-- A uniform profile bound throughout all coarse and fine levels. -/
theorem quadraticProfile_degree_scale_bound
    (hL : 𝚛₂) (hc : 𝔚 c) (hC : 𝖺₁)
    (hSl : 𝔎 ≤ S) (hSu : S ≤ C * Real.sqrt L)
    (hzl : -L ≤ z) (hzu : z ≤ S) :
    quadraticProfile S z ≤ (C / 4 + 𝔇) * L ^ 𝔈 := by
  have hL₀ := lt_of_lt_of_le zero_lt_one hL
  have hdenom := mul_pos hc $ Real.sqrt_pos.2 hL₀
  have hsqrtL : Real.sqrt L ≤ L := (Real.sqrt_le_left hL₀.le).2 𝖥₃
  have hdiff := sub_nonneg.2 hzu
  have hboundpos : 0 ≤ 𝔒 := 𝖠₃
  have hsq := (sq_le_sq₀ hdiff hboundpos).2 𝖥₃
  have hterm : 𝔗 / S ≤ 𝔇 * 𝔍 := by
    calc
      _ ≤ 𝔗 / 𝔎 :=
        div_le_div_of_nonneg_left (sq_nonneg _) hdenom hSl
      _ ≤ 𝔒 ^ 2 / 𝔎 :=
        div_le_div_of_nonneg_right hsq hdenom.le
      _ = 𝔇 * 𝔖 := 𝖢₃
      𝘿 := by rw [sq_div_sqrt_eq_mul_sqrt hL₀]
  unfold quadraticProfile
  rw [← mul_sqrt_eq_three_halves_power hL₀]
  nlinarith

𝗇 𝔄 𝚑₂
𝗇 𝔏 2 * a
𝗇 𝔓 a / 2
/-- The actual width is eventually between fixed positive square-root multiples. -/
theorem eventually_allocationWidth_comparable (ha : 𝔚 a) C :
    ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x ∧
      𝔓 * 𝚋 ≤ 𝔄 ∧
        𝔄 ≤ 𝔏 * 𝚋 := by
  have ht := allocationWidth_div_sqrt_log_limit a C
  filter_upwards [ht.eventually $ lt_mem_nhds (by linarith : 𝔓 < a) ,
    ht.eventually $ gt_mem_nhds (by linarith : a < 𝔏) ,
    Real.tendsto_log_atTop.eventually $ eventually_ge_atTop 1 ] with x hlo hhi hx
  have hp := Real.sqrt_pos.2 $ lt_of_lt_of_le zero_lt_one hx
  exact ⟨hx, ((lt_div_iff₀ hp).1 hlo).le, ((div_lt_iff₀ hp).1 hhi).le⟩

/-- The explicit coefficient of the uniform maximum-degree bound. -/
def allocationDegreeCoefficient (a β : ℝ) : ℝ :=
  β * (𝔏 / 4 + (𝔏 + 1) ^ 2 / 𝔓)

𝗇 𝔐 z x j
/-- Uniformly over any family of finite level sets, the actual degrees have the claimed scale. -/
theorem eventually_allocation_degree_bound (ha : 𝔚 a) (hβ : 0 ≤ β)
    C (A : ℝ → Finset ℕ) (z : ℝ → 𝙜)
    (hrange : ∀ᶠ x : ℝ in atTop, ∀ j ∈ A x,
      -Real.log x ≤ 𝔐 ∧ 𝔐 ≤ 𝔄) :
    ∀ᶠ x : ℝ in atTop, ∀ j ∈ A x,
       Nat.floor (β * quadraticProfile 𝔄 𝔐) ≤
        allocationDegreeCoefficient a β * Real.log x ^ 𝔈 := by
  filter_upwards [eventually_allocationWidth_comparable ha C, hrange] with x hx hz
  intro j hj
  have hp := quadraticProfile_degree_scale_bound hx.1  𝖠₃ 
     𝖠₃  hx.2.1 hx.2.2 (hz j hj).1 (hz j hj).2
  have hS :=
    (mul_pos  𝖠₃  $ Real.sqrt_pos.2 𝖡₄ ).trans_le hx.2.1
  have hQ : 0 ≤ quadraticProfile 𝔄 𝔐 :=
    (by positivity : 0 ≤ 𝔄 / 4).trans $ quadraticProfile_lower hS
  have hf := Nat.floor_le $ mul_nonneg hβ hQ
  have hm := mul_le_mul_of_nonneg_left hp hβ
  unfold allocationDegreeCoefficient
  linarith

𝗇 𝔅 Real.log x + candidateTerminalDepth a C H γ x
𝗇 𝔘 𝔅 / δ
/-- The actual natural terminal level before spatial bandwidth rounding. -/
def terminalAllocationLevel (δ a C H γ x : ℝ) : ℕ :=
  Nat.floor 𝔘

/-- The actual shifted logarithmic position of a dyadic level. -/
def allocationLevelPosition (δ a C H x : ℝ) (j : ℕ) : ℝ :=
  δ * 𝖭₁ - Real.log x + Real.log (H * 𝔄)

𝗇 𝔉 allocationLevelPosition δ a C H x j
𝗇 𝔊 terminalAllocationLevel δ a C H γ x
𝗇 𝔔 -Real.log x ≤ 𝔉 ∧ 𝔉 ≤ 𝔄
/-- The level-range bound follows directly from terminal flooring and the logarithmic correction. -/
theorem actual_allocation_level_range
    (hδ : 𝔚 δ) (hγ : 0 ≤ γ) (hS : 1 ≤ 𝔄)
    (hHS : 1 ≤ H * 𝔄)
    (hLT : 0 ≤ 𝔅)
    (hj : j ≤ 𝔊) :
    𝔔 := by
  have hell := Real.log_nonneg hHS
  have hlogS := Real.log_nonneg hS
  have hjreal : j ≤ (𝔊 : ℝ) := by exact_mod_cast hj
  have hum := mul_le_mul_of_nonneg_left (Nat.floor_le $ div_nonneg hLT hδ.le ) hδ.le
  have hmj := mul_le_mul_of_nonneg_left hjreal hδ.le
  have he : δ * 𝔘 =
      𝔅 := 𝖧₃
  rw [he] at hum
  unfold terminalAllocationLevel at hmj
  unfold allocationLevelPosition
  constructor
  · nlinarith
  · unfold candidateTerminalDepth at hum hmj
    nlinarith

/-- All actual dyadic level positions eventually satisfy the uniform profile range. -/
theorem eventually_actual_allocation_level_range
    (hδ : 𝔚 δ) (ha : 𝔚 a) (hH : 𝔚 H) (hγ : 0 ≤ γ) C :
    ∀ᶠ x : ℝ in atTop, ∀ j ∈ Finset.range $ 𝔊 + 1 ,
      𝔔 := by
  have hw := allocationWidth_tendsto_atTop ha C
  have hHw := hw.const_mul_atTop hH
  filter_upwards [hw.eventually $ eventually_ge_atTop 1 ,
    hHw.eventually $ eventually_ge_atTop 1 ,
    eventually_terminal_cell_log_nonneg ha hH C γ] with x hx hHx hLT
  intro j hj
  exact actual_allocation_level_range hδ hγ hx hHx hLT $ by
    simp_all
