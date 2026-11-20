module

public import HK.SBC5Family

/-!
# Five SBC agents with a constant digraph and oscillating convergence (this development)

`x(0) = (0, 7, 12 − √2, 19, 24)`, `r = (3, 9, 9, 9, 3)`;
`x(t) = (0, 6, 12, 18, 24) + ((1 − √2)/3)ᵗ (0, 1, −√2, 1, 0)`. The neighbourhood table
`{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}` is the same at every `t`, yet agents 1, 2, 3 alternate sides
of their limits. Hence Theorem 6.4(iv) and Conjecture 2.3 fail already with five SBC agents. This system
specializes the positive-radius family in `HK.SBC5Family` at `δ = 1`.
-/

public section

namespace HK

theorem sbc5Mode : Mode .sbc sbc5_r sbc5_x0 sbc5_lim sbc5_v sbc5Rate (fun _ => fiveRows) := by
  convert familyMode 1 zero_lt_one le_rfl using 1 <;> finite_check

corollary sbc5_closed_form := sbc5Mode.form

corollary sbc5_neighbors := sbc5Mode.orbit.table

corollary sbc5_fvct := sbc5Mode.final

corollary sbc5_perStepFactor := sbc5Mode.factor 1⋯3

end HK
