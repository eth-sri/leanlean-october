
import ImprovedExponents.Optimum.PerCBasic


/-!
# The crossing point of `γX(c, ·)` and `γ_Q`

Fix `c > 10`. On `[0, 9/10]` the function `γX(c, ·)` is continuous and strictly increasing from
`γX(c, 0) = 0`, and `γ_Q` is continuous and strictly decreasing from `γ_Q(0) = 2/3` to
`γ_Q(9/10) < 0`. So they cross at exactly one point `θ* ∈ (0, 9/10)` (`existsUnique_crossing`),
and `Γ(c) = sup_θ min(γX(c, θ), γ_Q(θ))` is their common value there (`Gam_eq_of_crossing`,
`exists_crossing_eq_Gam`). Consequences:

* `0 < Γ(c) < 2/3` (`Gam_pos`, `Gam_lt_two_thirds`);
* `min(γX(c, θ₀), γ_Q(θ₀)) ≤ Γ(c) ≤ max(γX(c, θ₀), γ_Q(θ₀))` for every `θ₀ ∈ (0, 9/10)`
  (`Gam_ge_min`, `Gam_le_max`);
* `Γ` is nondecreasing on `(10, ∞)` (`Gam_monotoneOn`).
-/

namespace ImprovedExponents

open Set

variable {c θ θ₀ : ℝ}

/-- For `c > 10` the functions `γX(c, ·)` and `γ_Q` cross in `(0, 9/10)`. -/
theorem exists_crossing (hc : 10 < c) : ∃ θ ∈ Ioo (0 : ℝ) (9 / 10), gammaX c θ = gammaQ θ := by
  have hcont : ContinuousOn (fun θ => gammaX c θ - gammaQ θ) (Icc 0 (9 / 10)) :=
    ((continuous_gammaX_right c).sub continuous_gammaQ).continuousOn
  have h0 : gammaX c 0 - gammaQ 0 < 0 := by
    simp
  have h1 : 0 < gammaX c (9 / 10) - gammaQ (9 / 10) := by
    grind [gammaX_pos, gammaQ_nine_tenths_neg]
  obtain ⟨θ, hθ, h⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 9 / 10) hcont ⟨h0, h1⟩
  grind

/-- `γX(c, ·)` increases strictly on `[0, 9/10]`, for `c > 10`. -/
theorem gammaX_strictMonoOn' (hc : 10 < c) : StrictMonoOn (gammaX c) (Icc 0 (9 / 10)) :=
  (gammaX_strictMonoOn hc).mono (by grind)

/-- At every `θ₀ ∈ [0, 9/10]`, the smaller of `γX(c, θ₀)` and `γ_Q(θ₀)` is at most the common
value at the crossing point. -/
theorem min_le_of_crossing (hc : 10 < c) (hθ : θ ∈ Ioo (0 : ℝ) (9 / 10))
    (h : gammaX c θ = gammaQ θ) (hθ₀ : θ₀ ∈ Icc (0 : ℝ) (9 / 10)) :
    min (gammaX c θ₀) (gammaQ θ₀) ≤ gammaX c θ := by
  have hθ' := Ioo_subset_Icc_self hθ
  rcases le_total θ₀ θ with h' | h'
  · exact (min_le_left _ _).trans ((gammaX_strictMonoOn' hc).monotoneOn hθ₀ hθ' h')
  · rw [h]
    exact (min_le_right _ _).trans (gammaQ_strictAntiOn.antitoneOn hθ' hθ₀ h')

/-- At every `θ₀ ∈ [0, 9/10]`, the larger of `γX(c, θ₀)` and `γ_Q(θ₀)` is at least the common
value at the crossing point. -/
theorem le_max_of_crossing (hc : 10 < c) (hθ : θ ∈ Ioo (0 : ℝ) (9 / 10))
    (h : gammaX c θ = gammaQ θ) (hθ₀ : θ₀ ∈ Icc (0 : ℝ) (9 / 10)) :
    gammaX c θ ≤ max (gammaX c θ₀) (gammaQ θ₀) := by
  have hθ' := Ioo_subset_Icc_self hθ
  rcases le_total θ θ₀ with h' | h'
  · exact ((gammaX_strictMonoOn' hc).monotoneOn hθ' hθ₀ h').trans (by simp)
  · rw [h]
    exact (gammaQ_strictAntiOn.antitoneOn hθ₀ hθ' h').trans (by simp)

/-- `Γ(c)` is the common value of `γX(c, ·)` and `γ_Q` at their crossing point. -/
theorem Gam_eq_of_crossing (hc : 10 < c) (hθ : θ ∈ Ioo (0 : ℝ) (9 / 10))
    (h : gammaX c θ = gammaQ θ) : Gam c = gammaX c θ := by
  refine IsGreatest.csSup_eq ⟨by grind, ?_⟩
  rintro _ ⟨θ₀, hθ₀, rfl⟩
  grind [min_le_of_crossing, Ioo_subset_Icc_self]

/-- For `c > 10` there is `θ* ∈ (0, 9/10)` with `γX(c, θ*) = Γ(c) = γ_Q(θ*)`. -/
theorem exists_crossing_eq_Gam (hc : 10 < c) :
    ∃ θ ∈ Ioo (0 : ℝ) (9 / 10), gammaX c θ = Gam c ∧ gammaQ θ = Gam c := by
  grind [exists_crossing, Gam_eq_of_crossing]

/-- `Γ(c) > 0` for `c > 10`. -/
theorem Gam_pos (hc : 10 < c := by linarith) : 0 < Gam c := by
  grind [exists_crossing_eq_Gam, gammaX_pos]

/-- `Γ(c) < 2/3` for `c > 10`. -/
theorem Gam_lt_two_thirds (hc : 10 < c) : Gam c < 2 / 3 := by
  obtain ⟨θ, hθ, -, hQ⟩ := exists_crossing_eq_Gam hc
  rw [← hQ, ← gammaQ_zero]
  exact gammaQ_strictAntiOn (by grind) (Ioo_subset_Icc_self hθ) hθ.1

/-- **Lower bound for `Γ`**: `min(γX(c, θ₀), γ_Q(θ₀)) ≤ Γ(c)` for every `θ₀ ∈ (0, 9/10)`. -/
theorem Gam_ge_min (hc : 10 < c) (hθ₀ : θ₀ ∈ Ioo (0 : ℝ) (9 / 10)) :
    min (gammaX c θ₀) (gammaQ θ₀) ≤ Gam c := by
  grind [exists_crossing, Gam_eq_of_crossing, min_le_of_crossing, Ioo_subset_Icc_self]

/-- **Upper bound for `Γ`**: `Γ(c) ≤ max(γX(c, θ₀), γ_Q(θ₀))` for every `θ₀ ∈ (0, 9/10)`. -/
theorem Gam_le_max (hc : 10 < c) (hθ₀ : θ₀ ∈ Ioo (0 : ℝ) (9 / 10)) :
    Gam c ≤ max (gammaX c θ₀) (gammaQ θ₀) := by
  grind [exists_crossing, Gam_eq_of_crossing, le_max_of_crossing, Ioo_subset_Icc_self]
