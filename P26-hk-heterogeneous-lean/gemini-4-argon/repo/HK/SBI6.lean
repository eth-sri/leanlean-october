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

local notation "sbi6_N" =>
  ![{0}, {0, 1, 2, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4, 5}, {2, 3, 4, 5}, {5}]

/- The table at time `t`. -/
theorem sbi6_closed_form t :
    tr6 t = aff(sbi6_lim, sbi6Rate ^ t, sbi6_v) :=
  traj_eigen (N := fun _ => sbi6_N)

theorem sbi6_neighbors t :
    nbi sbi6_r (tr6 t) = sbi6_N := nbh sbi6_closed_form

/-- The final value at constant topology (Definition 3.1) is the limit at every `t`. -/
theorem sbi6_fvct t : fvct .sbi sbi6_r (tr6 t) = sbi6_lim :=
  fvct_eigen sbi6_closed_form sbi6_neighbors

/-- The per-step convergence factor (Definition 6.1) of agents 1–4 is the rate at every `t`. -/
theorem sbi6_perStepFactor t i (hi : i ∈ ~{1, 2, 3, 4}) :
    perStepFactor .sbi sbi6_r tr6 i t = sbi6Rate :=
  perStepFactor_geom sbi6_closed_form sbi6_fvct

end HK
