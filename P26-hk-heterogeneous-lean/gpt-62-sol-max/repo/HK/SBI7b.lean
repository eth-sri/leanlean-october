module

public import HK.Basic

/-!
# The second 7-agent SBI system (Hegarty–Ognissanti–Wedin §5)

`x(0) = (0, 71, 100 − φ, 110, 120 + φ, 149, 220)`, `r = (85, 35, 35, 75, 35, 35, 85)`,
`λ = (1 − √5)/8`; `x(t) = (0, 70, 100, 110, 120, 150, 220) + λᵗ (0, 1, −φ, 0, φ, −1, 0)`. The
neighbourhood table is the same at every `t`, yet agents 1, 2, 4, 5 alternate sides of their limits;
their per-step convergence factor is `λ` at every `t`. Index 3 (the paper's agent 4) sits at its
limit.
-/

@[expose] public section

namespace HK

open Filter Topology

local notation "X" => traj Model.sbi sbi7b_r sbi7b_x0
local notation "N" => ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, {2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5, 6}, {6}]

attribute [local simp] sbi7b_x0 sbi7b_lim sbi_v sbi7b_r sbiRate_eq in
private theorem orbit : ModeOrbit .sbi sbi7b_r sbi7b_x0 sbi7b_lim sbi_v sbiRate
    (fun _ => N) where
  rate := sbiRate_decay
  table t := by
    obtain ⟨_, _⟩ := sbiRate_pow_bounds t
    have := Real.goldenRatio_pos
    have := Real.goldenRatio_lt_two
    check_neighbors [-sbiRate_eq]

theorem sbi7b_closed_form (t : ℕ) : X t = profile sbi7b_lim (sbiRate ^ t) sbi_v := orbit.form t

theorem sbi7b_neighbors (t : ℕ) : neighbors .sbi sbi7b_r (X t) = N := orbit.neighborhoods t

theorem sbi7b_digraph_constant (t : ℕ) :
    proximityDigraph .sbi sbi7b_r (X t) = proximityDigraph .sbi sbi7b_r sbi7b_x0 :=
  digraph_constant sbi7b_neighbors t

theorem sbi7b_facts : Tendsto X atTop (𝓝 sbi7b_lim) ∧ NeverStable X :=
  orbit.facts 1 (by norm_num [sbi_v])

theorem sbi7b_fvct (t : ℕ) : fvct .sbi sbi7b_r (X t) = sbi7b_lim :=
  orbit.frozenLimit t

theorem sbi7b_perStepFactor (t : ℕ) (i : Fin 7) (hi : i ∈ ({1, 2, 4, 5} : Finset (Fin 7))) :
    perStepFactor .sbi sbi7b_r X i t = sbiRate :=
  orbit.factor t i (by
    have := Real.goldenRatio_pos.ne'
    fin_cases i <;> simp_all [sbi_v])

theorem sbi7b_perStepFactor_not_tendsto (i : Fin 7) (hi : i ∈ ({1, 2, 4, 5} : Finset (Fin 7)))
    (ρ : ℝ) (hρ : 0 ≤ ρ) : ¬ Tendsto (fun t => perStepFactor .sbi sbi7b_r X i t) atTop (𝓝 ρ) :=
  orbit.factor_not_tendsto i (by
    have := Real.goldenRatio_pos.ne'
    fin_cases i <;> simp_all [sbi_v]) ρ hρ

end HK
