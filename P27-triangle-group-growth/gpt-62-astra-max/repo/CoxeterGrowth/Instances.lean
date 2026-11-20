module
public import CoxeterGrowth.Triangle

/-!
# Specializations of the triangle growth identity

We exhibit a matrix for each label pair and expand the geometric sums in three
small cases. For `(2,3,∞)` we transfer the computable initial counts, the Padovan
recurrence and the bounds from the model, and specialize the root limit.
-/

@[expose] public section

namespace TriangleGrowth

open Finset PowerSeries

/-- **(2) Non-vacuity**: the Coxeter matrix of type `(p, q, ∞)` exists for all `p, q ≥ 2`. -/
theorem triangle_matrix_exists (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    ∃ M : CoxeterMatrix (Fin 3), M 0 1 = 0 ∧ M 0 2 = p ∧ M 1 2 = q := by
  refine ⟨⟨!![1, 0, p; 0, 1, q; p, q, 1], .ext ?_, ?_, ?_⟩, rfl, rfl, rfl⟩ <;>
    intro i <;> fin_cases i <;> first
    | rfl
    | intro j; fin_cases j <;> first | rfl | dsimp; grind

variable {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)} (cs : CoxeterSystem M W)
  (h01 : M 0 1 = 0)

local macro "closed_series " b:ident c:ident : tactic => `(tactic|
  linear_combination (norm := (norm_num [sum_Ico_eq_sum_range, sum_range_succ]; ring1))
    growth_series ‹CoxeterSystem _ _› (by decide) (by decide) (by assumption) $b $c)

include h01

/-- **(4) `(2,4,∞)`.** -/
theorem growth_series_24 (h02 : M 0 2 = 2) (h12 : M 1 2 = 4) :
    growth cs * (1 - X ^ 2 - X ^ 3 - X ^ 4) = (1 + X) ^ 2 * (1 + X + X ^ 2 + X ^ 3) := by
  closed_series h02 h12

/-- **(5) `(3,3,∞)`.** -/
theorem growth_series_33 (h02 : M 0 2 = 3) (h12 : M 1 2 = 3) :
    growth cs * (1 - X ^ 2 - 2 * X ^ 3 - X ^ 4) = (1 + X) * (1 + X + X ^ 2) ^ 2 := by
  closed_series h02 h12

variable (h02 : M 0 2 = 2) (h12 : M 1 2 = 3)
include h02 h12

/-- **(3) `(2,3,∞)`.** -/
theorem growth_series_23 : growth cs * (1 - X ^ 2 - X ^ 3) = (1 + X) ^ 2 * (1 + X + X ^ 2) := by
  closed_series h02 h12

local notation "count_eq" => sphere_eq cs (by decide) (by decide) h01 h02 h12

/-- **(6) `(2,3,∞)` sphere sizes**: `1, 3, 5, 7, 9`, then `a(n+5) = a(n+3) + a(n+2)`. -/
theorem sphere23_values : aₙ cs 0 = 1 ∧ aₙ cs 1 = 3 ∧ aₙ cs 2 = 5 ∧ aₙ cs 3 = 7 ∧
    aₙ cs 4 = 9 ∧ ∀ n, aₙ cs (n + 5) = aₙ cs (n + 3) + aₙ cs (n + 2) := by
  simp [count_eq, count23_rec]
  decide +kernel

/-- **(7)** The recursion of (6) fails one step earlier: `a(4) ≠ a(2) + a(1)`. -/
theorem sphere23_rec_fails_at_4 : aₙ cs 4 ≠ aₙ cs 2 + aₙ cs 1 := by
  simp only [count_eq]
  decide +kernel

/-- **(8) Padovan**: `a(n) = Pad(n + 5)` for `n ≥ 2`. -/
theorem sphere23_padovan (pad : ℕ → ℕ) (h0 : pad 0 = 1) (h1 : pad 1 = 1) (h2 : pad 2 = 1)
    (hr : ∀ n, pad (n + 3) = pad (n + 1) + pad n) (n : ℕ) (hn : 2 ≤ n) :
    aₙ cs n = pad (n + 5) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [count_eq]
  apply count23_ind (P := fun k v => v = pad (k + 7))
  · intro k hk
    interval_cases k <;> dsimp <;> grind
  · rintro k _ _ rfl rfl
    exact (hr (k + 7)).symm

variable (ρ : ℝ) (hρ : 1 < ρ) (hc : ρ ^ 3 = ρ + 1)
include hρ hc

/-- **(10) Two-sided growth bound** for `(2,3,∞)`: `2ρⁿ ≤ a(n) ≤ 4ρⁿ`, `n ≥ 2`. -/
theorem sphere23_growth_bounds (n : ℕ) : Bounds ρ n (aₙ cs (n + 2)) := by
  simpa only [count_eq] using bounds23 ρ hρ hc n

/-- **(11) Growth rate** of `(2,3,∞)`: `a(n)^{1/n} → ρ`, the plastic number. -/
theorem sphere23_root_tendsto : RootLimit (n ↦ aₙ cs n) ρ :=
  sphere_root_tendsto_rate cs le_rfl (by decide) h01 h02 h12 ρ hρ ((eq23 hρ).2 hc)

end TriangleGrowth
