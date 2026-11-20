module

public import HK.Basic

/-!
# Six SBI agents with a constant digraph and oscillating convergence (this development)

`x_∞ = (0, 25, 31, 44, 55, 90)`, `v = (0, 10, −5 − √249, 8, 10, 0)/16`, `r = (45, 18, 27, 45/2, 27, 54)`,
`x(0) = x_∞ + v`, `x(t) = x_∞ + ((13 − √249)/40)ᵗ v`. The neighbourhood table
`{0}, {0, 1, 2, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4, 5}, {2, 3, 4, 5}, {5}` is the same at every `t`, yet
agents 1–4 alternate sides of their limits. Hence Theorem 6.4(iv) and Conjecture 2.3 fail already with
six SBI agents. The enclosure `15 < √249 < 16` bounds the rate; a single table works
throughout the resulting range `λ ≤ λᵗ ≤ 1`.
-/

public section

namespace HK

theorem sbi6Mode : Mode .sbi sbi6_r sbi6_x0 sbi6_lim sbi6_v sbi6Rate
    (fun _ => rows![{0}, 0⋯3, 0⋯4, {0, 2, 3, 4, 5}, 2⋯5, {5}]) := by
  radical 249
  certify

corollary sbi6_closed_form := sbi6Mode.form

corollary sbi6_neighbors := sbi6Mode.orbit.table

corollary sbi6_fvct := sbi6Mode.final

corollary sbi6_perStepFactor := sbi6Mode.factor 1⋯4

end HK
