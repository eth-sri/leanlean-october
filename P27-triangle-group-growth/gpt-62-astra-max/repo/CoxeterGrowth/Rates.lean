module
public import CoxeterGrowth.TriangleNF

/-!
# The equation for the exponential growth rate

`G p q τ` is the product of the two positive-degree geometric sums at `1 / τ`.
A positive exponential sequence with base `τ` satisfies the homogeneous counting
recurrence precisely when this product is one. On `[1, ∞)` the product is strictly
decreasing. We locate the crossing and compare it across different label pairs.
-/

@[expose] public section

namespace TriangleGrowth

open Finset Set

scoped notation:max "G " p:arg q:arg τ:arg => (S₊ p (τ⁻¹) * S₊ q (τ⁻¹))

variable {p q p' q' : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
include hp hq

theorem anti : StrictAntiOn (fun τ : ℝ => G p q τ) (Ici 1) := by
  intro x hx y hy hxy
  change 1 ≤ _ at hx hy
  simp only [geom_mul]
  refine sum_lt_sum_of_nonempty ⟨(1, 1), by simp; omega⟩ fun u hu => ?_
  gcongr
  grind

theorem below_one : G p q (2 : ℝ) < 1 := by
  have small (m) (hm : 2 ≤ m) : S₊ m (2 : ℝ)⁻¹ < 1 := by
    rw [geom_sum_Ico' (by norm_num) (by omega), div_lt_one (by norm_num)]
    norm_num
  simpa using mul_lt_mul'' (small p hp) (small q hq) (by positivity) (by positivity)

theorem above_one : 1 < G p q (1 : ℝ) ↔ (p, q) ≠ (2, 2) := by
  simp [← Nat.cast_mul, Nat.one_lt_mul_iff]
  grind

/-- **(15) The rate equation** has exactly one root `τ > 1` for every hyperbolic `(p, q)`. -/
theorem rate_exists_unique (hne : (p, q) ≠ (2, 2)) :
    ∃! τ : ℝ, 1 < τ ∧ G p q τ = 1 := by
  obtain ⟨x, hx, H⟩ := intermediate_value_Ioo' (f := fun x : ℝ => G p q x)
    (by norm_num : (1 : ℝ) ≤ 2) (by fun_prop (disch := intros; grind))
    ⟨below_one hp hq, (above_one hp hq).2 hne⟩
  exact ⟨x, ⟨hx.1, H⟩, fun y hy => (anti hp hq).injOn hy.1.le hx.1.le (hy.2.trans H.symm)⟩

omit hp hq

theorem eq23 {x : ℝ} (hx : 1 < x) : G 2 3 x = 1 ↔ x ^ 3 = x + 1 := by
  norm_num [sum_Ico_eq_sum_range, sum_range_succ]
  field_simp
  grind

/-- **(9)** The plastic number exists and is unique. -/
theorem plastic_exists_unique : ∃! ρ : ℝ, 1 < ρ ∧ ρ ^ 3 = ρ + 1 :=
  (existsUnique_congr fun _ => and_congr_right fun hx => eq23 hx).1
    (rate_exists_unique (by decide) (by decide) (by decide))

section
variable (hpp : p ≤ p') (hqq : q ≤ q') (hne : (p, q) ≠ (p', q')) (τ τ' : ℝ) (hτ : 1 < τ)
  (hτ' : 1 < τ') (heq : G p q τ = 1) (heq' : G p' q' τ' = 1)
include hp hq hτ heq

include hpp hqq hne hτ' heq' in
/-- **(17) The rate is strictly increasing** in `(p, q)`. -/
theorem rate_lt_rate : τ < τ' := by
  apply ((anti (hp.trans hpp) (hq.trans hqq)).lt_iff_gt hτ'.le hτ.le).mp
  rw [heq', ← heq, geom_mul, geom_mul]
  -- The far corner of the larger rectangle contributes a new positive summand.
  refine sum_lt_sum_of_subset (by intro u hu; grind)
    (i := (p' - 1, q' - 1)) ?_ ?_ (by positivity) (by intros; positivity) <;> grind

/-- **(18) The plastic number is the minimal rate**: `ρ ≤ τ`, with equality exactly for
`(p, q) = (2, 3)` and `(3, 2)`. -/
theorem plastic_le_rate (ρ : ℝ) (hρ : 1 < ρ)
    (hc : ρ ^ 3 = ρ + 1) : ρ ≤ τ ∧ (τ = ρ ↔ (p = 2 ∧ q = 3) ∨ (p = 3 ∧ q = 2)) := by
  have hr := (eq23 hρ).2 hc
  wlog h : p ≤ q generalizing p q
  · have := this hq hp (by rwa [mul_comm]) (by omega)
    grind
  -- A crossing above 1 excludes (2,2). In sorted order this forces q ≥ 3.
  have := (above_one hp hq).1 (heq ▸ anti hp hq le_rfl hτ.le hτ)
  by_cases same : (2, 3) = (p, q)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    have := (anti hp hq).injOn hτ.le hρ.le (heq.trans hr.symm)
    grind
  · have := rate_lt_rate le_rfl (by decide) hp (by grind) same ρ τ hρ hτ hr heq
    grind

/-- **(19)** Every rate is below `2`. -/
theorem rate_lt_two : τ < 2 :=
  ((anti hp hq).lt_iff_gt (by norm_num : (1 : ℝ) ≤ 2) hτ.le).mp (heq.symm ▸ below_one hp hq)

end

/-- **(20)** The rates tend to `2` as `p, q → ∞`. -/
theorem rate_tendsto_two (σ : ℝ) (hσ : σ < 2) : ∃ N : ℕ, ∀ p q : ℕ, N ≤ p → N ≤ q →
    ∀ τ : ℝ, 1 < τ → G p q τ = 1 → σ < τ := by
  rcases le_or_gt σ 1 with h | h
  · exact ⟨0, fun _ _ _ _ _ hτ _ => h.trans_lt hτ⟩
  have hx1 := inv_lt_one_of_one_lt₀ h
  -- The geometric sum from 1 to m-1 exceeds 1 once σ⁻ᵐ < 2/σ - 1.
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hx1).eventually_lt_const
      (by field_simp; linarith : 0 < 2 * σ⁻¹ - 1))
  refine ⟨max N 2, fun p q hp hq τ hτ heq => ?_⟩
  have H (m) (hm : max N 2 ≤ m) : 1 < S₊ m σ⁻¹ := by
    rw [geom_sum_Ico' hx1.ne (by omega), lt_div_iff₀ (sub_pos.2 hx1), pow_one, one_mul]
    linarith [hN m (by omega)]
  apply ((anti (by omega : 2 ≤ p) (by omega : 2 ≤ q)).lt_iff_gt hτ.le h.le).mp
  rw [heq]
  exact one_lt_mul (H p hp).le (H q hq)

end TriangleGrowth
