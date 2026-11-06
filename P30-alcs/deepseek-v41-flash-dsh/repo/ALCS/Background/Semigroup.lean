module

public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Strongly continuous semigroups

`C0Semigroup 𝕜 X` : strongly continuous semigroups `T` on `X`: `T 0 = Id`,
`T (t + s) = T t ∘ T s` for `t, s ≥ 0`, and `T t y → y` as `t → 0⁺` for every `y`.

Only the strong continuity at `0` is used below: the continuity of the orbits
(Proposition 1.2 of the paper) is not needed for the two main results.

`T` is a function `ℝ → (X →L[𝕜] X)`; all axioms only involve nonnegative times, so the
values of `T t` for `t < 0` play no role.
-/

open Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A strongly continuous semigroup on `X`. -/
structure C0Semigroup (𝕜 : Type*) (X : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] where
  /-- the operators `T t` -/
  T : ℝ → X →L[𝕜] X
  /-- `T 0 = Id` -/
  T_zero : T 0 = ContinuousLinearMap.id 𝕜 X
  /-- `T (t + s) = T t ∘ T s` for `t, s ≥ 0` -/
  T_add : ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → T (t + s) = (T t).comp (T s)
  /-- `T t y → y` as `t → 0⁺`, for every `y` -/
  T_cont : ∀ y : X, Tendsto (fun t => T t y) (nhdsWithin 0 (Set.Ici 0)) (𝓝 y)

namespace C0Semigroup

variable (S : C0Semigroup 𝕜 X)

/-- `‖T t‖ ≤ M` on some interval `[0, τ]` (Banach–Steinhaus). -/
theorem exists_bound_near_zero [CompleteSpace X] :
    ∃ τ > 0, ∃ M ≥ 1, ∀ t, 0 ≤ t → t ≤ τ → ‖S.T t‖ ≤ M := by
  by_contra h
  have key : ∀ n : ℕ, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 < ‖S.T t‖ := by
    intro n
    by_contra hn
    push Not at hn
    exact h ⟨1 / ((n : ℝ) + 1), by positivity, (n : ℝ) + 1,
      le_add_of_nonneg_left (by positivity), hn⟩
  choose t ht0 htle htbig using key
  have ht_lim : Tendsto t atTop (nhdsWithin 0 (Set.Ici 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨squeeze_zero ht0 htle tendsto_one_div_add_atTop_nhds_zero_nat,
      Filter.Eventually.of_forall (fun n => ht0 n)⟩
  have hbdd : ∀ x : X, ∃ C, ∀ n, ‖S.T (t n) x‖ ≤ C := by
    intro x
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1
      (Metric.isBounded_range_of_tendsto _ ((S.T_cont x).comp ht_lim))
    exact ⟨C, fun n => hC _ (Set.mem_range_self n)⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hbdd
  obtain ⟨n, hn⟩ := exists_nat_gt C
  linarith [hC n, htbig n]

/-- `T (a + h) y - T a y = T a (T h y - y)` -/
theorem orbit_sub (y : X) (a h : ℝ) (ha : 0 ≤ a) (hh : 0 ≤ h) :
    S.T (a + h) y - S.T a y = S.T a (S.T h y - y) := by
  rw [S.T_add a h ha hh, ContinuousLinearMap.comp_apply, map_sub]

end C0Semigroup
