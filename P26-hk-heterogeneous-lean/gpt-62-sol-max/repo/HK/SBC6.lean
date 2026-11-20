module

public import HK.Basic

/-!
# The 6-agent SBC system (Hegarty–Ognissanti–Wedin §4)

`x(0) = (0, 22, 37, 103, 118, 140)`, `r = (10, 70, 70, 70, 70, 10)`;
`x(t) = (0, 20, 40, 100, 120, 140) + (−1/6)ᵗ (0, 2, −3, 3, −2, 0)`. The neighbourhood table is the
same at every `t` (so the proximity digraph is constant), yet agents 1–4 alternate sides of their
limits; their per-step convergence factor (Definition 6.1, with the final value at constant topology
of Definition 3.1 equal to the limit) is `−1/6` at every `t`.
-/

@[expose] public section

namespace HK

open Filter Topology

local notation "q" => (-1 / 6 : ℝ)
local notation "X" => traj Model.sbc sbc6_r sbc6_x0
local notation "N" => ![{0}, {0, 1, 2}, {0, 1, 2, 3}, {2, 3, 4, 5}, {3, 4, 5}, {5}]

attribute [local simp] sbc6_x0 sbc6_lim sbc6_v sbc6_r in
private theorem orbit : ModeOrbit .sbc sbc6_r sbc6_x0 sbc6_lim sbc6_v q
    (fun _ => N) where
  table t := by
    obtain ⟨_, _⟩ := sixth_pow_bounds t
    check_neighbors []

theorem sbc6_closed_form (t : ℕ) : X t = profile sbc6_lim (q ^ t) sbc6_v := orbit.form t

theorem sbc6_neighbors (t : ℕ) : neighbors .sbc sbc6_r (X t) = N := orbit.neighborhoods t

theorem sbc6_digraph_constant (t : ℕ) :
    proximityDigraph .sbc sbc6_r (X t) = proximityDigraph .sbc sbc6_r sbc6_x0 :=
  digraph_constant sbc6_neighbors t

theorem sbc6_facts : Tendsto X atTop (𝓝 sbc6_lim) ∧ NeverStable X :=
  orbit.facts 1 (by norm_num [sbc6_v])

theorem sbc6_fvct (t : ℕ) : fvct .sbc sbc6_r (X t) = sbc6_lim :=
  orbit.frozenLimit t

theorem sbc6_perStepFactor (t : ℕ) (i : Fin 6) (hi : i ∈ ({1, 2, 3, 4} : Finset (Fin 6))) :
    perStepFactor .sbc sbc6_r X i t = q :=
  orbit.factor t i (by fin_cases i <;> simp_all [sbc6_v])

theorem sbc6_perStepFactor_not_tendsto (i : Fin 6) (hi : i ∈ ({1, 2, 3, 4} : Finset (Fin 6)))
    (ρ : ℝ) (hρ : 0 ≤ ρ) : ¬ Tendsto (fun t => perStepFactor .sbc sbc6_r X i t) atTop (𝓝 ρ) :=
  orbit.factor_not_tendsto i (by fin_cases i <;> simp_all [sbc6_v]) ρ hρ

end HK
