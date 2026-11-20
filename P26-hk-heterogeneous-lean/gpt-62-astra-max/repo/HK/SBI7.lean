module

public import HK.Basic

/-!
# The 7-agent SBI system (Hegarty–Ognissanti–Wedin §3)

`x(0) = (0, 15/2, 10 − φ/2, 11, 12 + φ/2, 29/2, 22)`, `r = (8, 4, 4, 8, 4, 4, 8)`, `φ = (1 + √5)/2`,
`λ = (1 − √5)/8`; `x(t) = (0, 7, 10, 11, 12, 15, 22) + (λᵗ/2) (0, 1, −φ, 0, φ, −1, 0)`. The middle
agent (index 3) listens to indices 1–5 at even `t` and to 2, 3, 4 at odd `t`; the proximity digraph
is never eventually constant; agents 1, 2, 4, 5 alternate sides of their limits. The tables are
checked on `λ ≤ u ≤ 1` with `u` positive at even times and negative at odd times.
-/

public section

namespace HK

set_option maxHeartbeats 450000 in
theorem sbi7Mode : Mode .sbi sbi7_r sbi7_x0 sbi7_lim ((1 / 2 : ℝ) • sbi_v) sbiRate
    (fun t => rows![{0}, 0⋯3, 1⋯4, if Even t then 1⋯5 else 2⋯4, 2⋯5, 3⋯6, {6}]) := by
  radical 5
  certify

corollary sbi7_closed_form := sbi7Mode.form fun t i => sbiRate ^ t / 2 * sbi_v i

corollary sbi7_neighbors := sbi7Mode.orbit.table

corollary sbi7_digraph_not_eventually_constant := sbi7Mode.orbit.changes

end HK
