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

public section

namespace HK

theorem sbi7bMode : Mode .sbi sbi7b_r sbi7b_x0 sbi7b_lim sbi_v sbiRate
    (fun _ => rows![{0}, 0⋯3, 1⋯4, 2⋯4, 2⋯5, 3⋯6, {6}]) := by
  radical 5
  certify

corollary sbi7b_closed_form := sbi7bMode.form

corollary sbi7b_neighbors := sbi7bMode.orbit.table

corollary sbi7b_digraph_constant := sbi7bMode.orbit.constant

corollary sbi7b_fvct := sbi7bMode.final

corollary sbi7b_perStepFactor := sbi7bMode.factor {1, 2, 4, 5}

corollary sbi7b_perStepFactor_not_tendsto := sbi7bMode.noFactorLimit _ sbi7b_perStepFactor

end HK
