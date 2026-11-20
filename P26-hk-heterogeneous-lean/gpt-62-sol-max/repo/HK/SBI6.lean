module

public import HK.Basic

/-!
# Six SBI agents with a constant digraph and oscillating convergence (this development)

`x_∞ = (0, 25, 31, 44, 55, 90)`, `v = (0, 10, −5 − √249, 8, 10, 0)/16`, `r = (45, 18, 27, 45/2, 27, 54)`,
`x(0) = x_∞ + v`, `x(t) = x_∞ + ((13 − √249)/40)ᵗ v`. The neighbourhood table
`{0}, {0, 1, 2, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4, 5}, {2, 3, 4, 5}, {5}` is the same at every `t`, yet
agents 1–4 alternate sides of their limits. Hence Theorem 6.4(iv) and Conjecture 2.3 fail already with
six SBI agents. The identities used: `√249² = 249`; the rate `λ = (13 − √249)/40` satisfies
`40λ = 13 − √249` and `λ² = (13/20)λ + 1/20`; `15 < √249 < 16` gives `−3/40 < λ < −1/20`, so
`λ ≤ λᵗ ≤ 1` for every `t` and one table serves both parities.
-/

@[expose] public section

namespace HK

open Filter Topology

local notation "X" => traj Model.sbi sbi6_r sbi6_x0
local notation "N" => ![{0}, {0, 1, 2, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4, 5}, {2, 3, 4, 5}, {5}]

private theorem root_bound : Real.sqrt 249 < 16 := by norm_num [Real.sqrt_lt']

private theorem rate_bounds : -3 / 40 < sbi6Rate ∧ sbi6Rate < 0 := by
  have hlo : 15 < Real.sqrt 249 := by norm_num [Real.lt_sqrt]
  unfold sbi6Rate
  constructor <;> linarith [root_bound]

attribute [local simp] sbi6_x0 sbi6_lim sbi6_v sbi6_r sbi6Rate in
private theorem orbit : ModeOrbit .sbi sbi6_r sbi6_x0 sbi6_lim sbi6_v sbi6Rate
    (fun _ => N) where
  rate := ⟨by linarith [rate_bounds.1], rate_bounds.2⟩
  table t := by
    obtain ⟨_, _⟩ := neg_pow_bounds (by norm_num) rate_bounds.1.le rate_bounds.2.le t
    have := Real.sqrt_nonneg 249
    have := root_bound
    check_neighbors [-sbi6Rate]

theorem sbi6_closed_form (t : ℕ) : X t = profile sbi6_lim (sbi6Rate ^ t) sbi6_v := orbit.form t

theorem sbi6_neighbors (t : ℕ) : neighbors .sbi sbi6_r (X t) = N := orbit.neighborhoods t

theorem sbi6_digraph_constant (t : ℕ) :
    proximityDigraph .sbi sbi6_r (X t) = proximityDigraph .sbi sbi6_r sbi6_x0 :=
  digraph_constant sbi6_neighbors t

theorem sbi6_facts : Tendsto X atTop (𝓝 sbi6_lim) ∧ NeverStable X :=
  orbit.facts 1 (by norm_num [sbi6_v])

private theorem r_pos : ∀ i, 0 < sbi6_r i := by norm_num [Fin.forall_fin_succ, sbi6_r]

theorem not_conjecture23_sbi_six : ¬ Conjecture23ForAgents .sbi 6 := refute23 r_pos sbi6_facts.2

theorem not_theorem64iv_sbi_six : ¬ Theorem64ivForAgents .sbi 6 :=
  refute64 r_pos sbi6_digraph_constant sbi6_facts.2

theorem sbi6_fvct (t : ℕ) : fvct .sbi sbi6_r (X t) = sbi6_lim :=
  orbit.frozenLimit t

theorem sbi6_perStepFactor (t : ℕ) (i : Fin 6) (hi : i ∈ ({1, 2, 3, 4} : Finset (Fin 6))) :
    perStepFactor .sbi sbi6_r X i t = sbi6Rate :=
  orbit.factor t i (by
    fin_cases i <;> simp_all [sbi6_v]
    linarith [Real.sqrt_nonneg 249])

end HK
