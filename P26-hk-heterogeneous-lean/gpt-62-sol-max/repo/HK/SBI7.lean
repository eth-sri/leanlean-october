module

public import HK.Basic

/-!
# The 7-agent SBI system (Hegarty–Ognissanti–Wedin §3)

`x(0) = (0, 15/2, 10 − φ/2, 11, 12 + φ/2, 29/2, 22)`, `r = (8, 4, 4, 8, 4, 4, 8)`, `φ = (1 + √5)/2`,
`λ = (1 − √5)/8`; `x(t) = (0, 7, 10, 11, 12, 15, 22) + (λᵗ/2) (0, 1, −φ, 0, φ, −1, 0)`. The middle
agent (index 3) listens to indices 1–5 at even `t` and to 2, 3, 4 at odd `t`; the proximity digraph
is never eventually constant; agents 1, 2, 4, 5 alternate sides of their limits. The table uses
the sign of `λᵗ` and the bounds `−1/4 ≤ λᵗ ≤ 1` and `0 < φ < 2`. The averaging identity uses
`φ² = φ + 1`.
-/

@[expose] public section

namespace HK

open Filter Topology

local notation "X" => traj Model.sbi sbi7_r sbi7_x0
local notation "N[" t "]" =>
  ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, ite (Even t) {1, 2, 3, 4, 5} {2, 3, 4},
    {2, 3, 4, 5}, {3, 4, 5, 6}, {6}]

attribute [local simp] sbi7_x0 sbi7_lim sbi_v sbi7_r sbiRate_eq in
private theorem orbit : ModeOrbit .sbi sbi7_r sbi7_x0 sbi7_lim ((1 / 2 : ℝ) • sbi_v) sbiRate
    (fun t => N[t]) where
  rate := sbiRate_decay
  table t := by
    obtain ⟨_, _⟩ := sbiRate_pow_bounds t
    have := Real.goldenRatio_pos
    have := Real.goldenRatio_lt_two
    have hp (h : Even t) := h.pow_pos sbiRate_neg.ne
    have hn (h : ¬ Even t) := (Nat.not_even_iff_odd.mp h).pow_neg sbiRate_neg
    simp only [← mul_smul]
    check_neighbors [mem_ite, -sbiRate_eq]

theorem sbi7_closed_form (t : ℕ) : X t = profile sbi7_lim (sbiRate ^ t / 2) sbi_v := by
  change _ = sbi7_lim + (sbiRate ^ t / 2) • sbi_v
  simpa only [← mul_smul, div_eq_mul_inv, one_mul] using orbit.form t

theorem sbi7_neighbors (t : ℕ) : neighbors .sbi sbi7_r (X t) = N[t] := orbit.neighborhoods t

theorem sbi7_digraph_not_eventually_constant (τ : ℕ) :
    ∃ t, τ ≤ t ∧ proximityDigraph .sbi sbi7_r (X t) ≠ proximityDigraph .sbi sbi7_r (X τ) := by
  refine ⟨τ + 1, Nat.le_succ _, ?_⟩
  by_cases ht : Even τ <;> simp [digraph_eq_iff, sbi7_neighbors, Nat.even_add_one, ht] <;> decide

theorem sbi7_facts : Tendsto X atTop (𝓝 sbi7_lim) ∧ NeverStable X :=
  orbit.facts 1 (by norm_num [Pi.smul_apply, sbi_v])

theorem sbi7_fvct (t : ℕ) : fvct .sbi sbi7_r (X t) = sbi7_lim :=
  orbit.frozenLimit t

end HK
