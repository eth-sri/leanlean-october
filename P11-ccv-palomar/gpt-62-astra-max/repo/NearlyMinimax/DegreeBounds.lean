module

public import NearlyMinimax.Allocation
public import NearlyMinimax.SaddleAsymptotics

@[expose] public section

/-!
# Uniform scalar bounds for the floored allocation degrees

These lemmas prove the `O(log(n)^(3/2))` maximum-degree bound in the upper
allocation, from the explicit width and the actual scalar level-range bounds.
The ensuing sample-size comparison is uniform in the number of levels.
-/

noncomputable section
open Filter
open scoped Topology

namespace NearlyMinimax

section
variable {L a : ℝ}

theorem mul_sqrt_eq_three_halves_power (hL : 0 < L) :
    L * Real.sqrt L = L ^ (3 / 2 : ℝ) := Eq.trans (Eq.trans (by rw [Real.rpow_one, Real.sqrt_eq_rpow]) ((Real.rpow_add hL 1 (1 / 2)).symm)) (by norm_num)

/-- A uniform profile bound throughout all coarse and fine levels. -/
theorem quadraticProfile_degree_scale_bound {S z c C : ℝ}
    (hL : 1 ≤ L) (hc : 0 < c) (hC : 0 ≤ C)
    (hSl : c * Real.sqrt L ≤ S) (hSu : S ≤ C * Real.sqrt L)
    (hzl : -L ≤ z) (hzu : z ≤ S) :
    let ratio := (C + 1) ^ 2 / c
    quadraticProfile S z ≤ (C / 4 + ratio) * L ^ (3 / 2 : ℝ) := by
  intro ratio
  have hL₀  := lt_of_lt_of_le zero_lt_one hL
  have hdenom  := mul_pos hc (Real.sqrt_pos.2 hL₀)
  have hsqrtL : Real.sqrt L ≤ L := (Real.sqrt_le_left hL₀.le).2 (by nlinarith)
  have hboundpos : 0 ≤ (C + 1) * L := by positivity
  have hsq  := (sq_le_sq₀ (sub_nonneg.2 hzu) hboundpos).2 (by nlinarith)
  have hterm : (S - z) ^ 2 / S ≤ (ratio) * (L * Real.sqrt L) := by
    calc
      _ ≤ _ :=
        by bound
      _ ≤ _ :=
        div_le_div_of_nonneg_right hsq hdenom.le
      _ = (ratio) * (L ^ 2 / Real.sqrt L) := by ring
      _ = _ := by rw [(by grind : L ^ 2 / √L = L * √L)]
  unfold quadraticProfile
  rw [← mul_sqrt_eq_three_halves_power hL₀]
  nlinarith

/-- The actual width is eventually between fixed positive square-root multiples. -/
theorem eventually_allocationWidth_comparable (ha : 0 < a) (C : ℝ) :
    ∀ᶠ x in atTop, 1 ≤ Real.log x ∧
      (a / 2) * Real.sqrt (Real.log x) ≤ allocationWidth a C x ∧
        allocationWidth a C x ≤ (2 * a) * Real.sqrt (Real.log x) := by
  have ht := allocationWidth_div_sqrt_log_limit a C
  filter_upwards [ht.eventually (lt_mem_nhds (by linarith : a / 2 < a)),
    ht.eventually (gt_mem_nhds (by linarith : a < 2 * a)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)] with x hlo hhi hx
  have hp  := Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hx)
  exact ⟨hx, ((lt_div_iff₀ hp).1 hlo).le, ((div_lt_iff₀ hp).1 hhi).le⟩

/-- The explicit coefficient of the uniform maximum-degree bound. -/
def allocationDegreeCoefficient (a β : ℝ) : ℝ :=
  β * ((2 * a) / 4 + (2 * a + 1) ^ 2 / (a / 2))

/-- Uniformly over any family of finite level sets, the actual degrees have the claimed scale. -/
theorem eventually_allocation_degree_bound {β : ℝ} (ha : 0 < a) (hβ : 0 ≤ β)
    {C : ℝ} {A : ℝ → Finset ℕ} {z : ℝ → ℕ → ℝ}
    (hrange : ∀ᶠ x in atTop, ∀ j ∈ A x,
      -Real.log x ≤ z x j ∧ z x j ≤ allocationWidth a C x) :
    ∀ᶠ x in atTop, ∀ j ∈ A x,
      (Nat.floor (β * quadraticProfile (allocationWidth a C x) (z x j))) ≤
        allocationDegreeCoefficient a β * (Real.log x) ^ (3 / 2 : ℝ) := by
  filter_upwards [eventually_allocationWidth_comparable ha C, hrange] with x hx hz
  intro j hj
  have hp := quadraticProfile_degree_scale_bound hx.1 (by positivity)
    (by positivity) hx.2.1 hx.2.2 (hz j hj).1 (hz j hj).2
  have hS  :=
    (mul_pos (by positivity) (Real.sqrt_pos.2 (by linarith))).trans_le hx.2.1
  have hQ : 0 ≤ quadraticProfile (allocationWidth a C x) (z x j) :=
    (by positivity : 0 ≤ allocationWidth a C x / 4).trans (quadraticProfile_lower hS)
  have hf := Nat.floor_le (mul_nonneg hβ hQ)
  have hm := mul_le_mul_of_nonneg_left hp hβ
  unfold allocationDegreeCoefficient
  linarith

end

section
variable (δ a C H γ x : ℝ)

/-- The actual natural terminal level before spatial bandwidth rounding. -/
def terminalAllocationLevel : ℕ :=
  Nat.floor ((Real.log x + candidateTerminalDepth a C H γ x) / δ)

/-- The actual shifted logarithmic position of a dyadic level. -/
def allocationLevelPosition (j : ℕ) : ℝ :=
  δ * j - Real.log x + Real.log (H * allocationWidth a C x)

end

variable {δ a C H γ : ℝ}

/-- The level-range bound follows directly from terminal flooring and the logarithmic correction. -/
theorem actual_allocation_level_range {x : ℝ} {j : ℕ}
    (hδ : 0 < δ) (hγ : 0 ≤ γ) (hS : 1 ≤ allocationWidth a C x)
    (hHS : 1 ≤ H * allocationWidth a C x)
    (hLT : 0 ≤ Real.log x + candidateTerminalDepth a C H γ x)
    (hj : j ≤ terminalAllocationLevel δ a C H γ x) :
    -Real.log x ≤ allocationLevelPosition δ a C H x j ∧
      allocationLevelPosition δ a C H x j ≤ allocationWidth a C x := by
  have hell  := Real.log_nonneg hHS
  have hlogS  := Real.log_nonneg hS
  have hjreal : j ≤ (terminalAllocationLevel δ a C H γ x : ℝ) := by exact_mod_cast hj
  have hum := mul_le_mul_of_nonneg_left (Nat.floor_le (div_nonneg hLT hδ.le)) hδ.le
  have hmj := mul_le_mul_of_nonneg_left hjreal hδ.le
  have he : δ * ((Real.log x + candidateTerminalDepth a C H γ x) / δ) =
      Real.log x + candidateTerminalDepth a C H γ x := by field_simp
  rw [he] at hum
  unfold terminalAllocationLevel at hmj
  unfold allocationLevelPosition
  constructor
  · linarith [mul_nonneg hδ.le (Nat.cast_nonneg j)]
  · unfold candidateTerminalDepth at hum hmj
    linarith [mul_nonneg hγ hlogS]

/-- All actual dyadic level positions eventually satisfy the uniform profile range. -/
theorem eventually_actual_allocation_level_range
    (hδ : 0 < δ) (ha : 0 < a) (hH : 0 < H) (hγ : 0 ≤ γ) (C : ℝ) :
    ∀ᶠ x in atTop, ∀ j ∈ Finset.range (terminalAllocationLevel δ a C H γ x + 1),
      -Real.log x ≤ allocationLevelPosition δ a C H x j ∧
        allocationLevelPosition δ a C H x j ≤ allocationWidth a C x := by
  have hw := allocationWidth_tendsto_atTop ha C
  filter_upwards [hw.eventually (eventually_ge_atTop 1),
    (hw.const_mul_atTop hH).eventually (eventually_ge_atTop 1),
    eventually_terminal_cell_log_nonneg ha hH C γ] with x hx hHx hLT
  intro j hj
  grind [actual_allocation_level_range]

end NearlyMinimax
