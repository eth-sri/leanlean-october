module

public import HK.Basic

/-!
# The 7-agent SBC system (Hegarty–Ognissanti–Wedin §2)

`x(0) = (0, 38, 69, 84, 99, 130, 168)`, `r = (18, 42, 48, 12, 48, 42, 18)`;
`x(t) = (0, 36, 72, 84, 96, 132, 168) + (−1/6)ᵗ (0, 2, −3, 0, 3, −2, 0)`. The middle agent (index 3)
listens to itself alone at even `t` and to indices 2, 3, 4 at odd `t`; the proximity digraph is
never eventually constant; agents 1, 2, 4, 5 alternate sides of their limits.
-/

@[expose] public section

namespace HK

open Filter Topology

local notation "q" => (-1 / 6 : ℝ)
local notation "X" => traj Model.sbc sbc7_r sbc7_x0
local notation "N[" t "]" =>
  ![{0}, {0, 1, 2}, {1, 2, 3, 4}, ite (Even t) {3} {2, 3, 4}, {2, 3, 4, 5}, {4, 5, 6}, {6}]

attribute [local simp] sbc7_x0 sbc7_lim sbc7_v sbc7_r in
private theorem orbit : ModeOrbit .sbc sbc7_r sbc7_x0 sbc7_lim sbc7_v q
    (fun t => N[t]) where
  table t := by
    obtain ⟨_, _⟩ := sixth_pow_bounds t
    have hp (h : Even t) := h.pow_pos (by norm_num : q ≠ 0)
    have hn (h : ¬ Even t) := (Nat.not_even_iff_odd.mp h).pow_neg (by norm_num : q < 0)
    check_neighbors [mem_ite]

theorem sbc7_closed_form (t : ℕ) : X t = profile sbc7_lim (q ^ t) sbc7_v := orbit.form t

theorem sbc7_neighbors (t : ℕ) : neighbors .sbc sbc7_r (X t) = N[t] := orbit.neighborhoods t

theorem sbc7_digraph_not_eventually_constant (τ : ℕ) :
    ∃ t, τ ≤ t ∧ proximityDigraph .sbc sbc7_r (X t) ≠ proximityDigraph .sbc sbc7_r (X τ) := by
  refine ⟨τ + 1, Nat.le_succ _, ?_⟩
  by_cases ht : Even τ <;> simp [digraph_eq_iff, sbc7_neighbors, Nat.even_add_one, ht] <;> decide

theorem sbc7_facts : Tendsto X atTop (𝓝 sbc7_lim) ∧ NeverStable X :=
  orbit.facts 1 (by norm_num [sbc7_v])

theorem sbc7_fvct (t : ℕ) : fvct .sbc sbc7_r (X t) = sbc7_lim :=
  orbit.frozenLimit t

end HK
