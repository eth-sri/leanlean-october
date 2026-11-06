module

public import HK.Basic

/-!
# The 7-agent SBI system (Hegarty–Ognissanti–Wedin §3)

`x(0) = (0, 15/2, 10 − φ/2, 11, 12 + φ/2, 29/2, 22)`, `r = (8, 4, 4, 8, 4, 4, 8)`, `φ = (1 + √5)/2`,
`λ = (1 − √5)/8`; `x(t) = (0, 7, 10, 11, 12, 15, 22) + (λᵗ/2) (0, 1, −φ, 0, φ, −1, 0)`. The middle
agent (index 3) listens to indices 1–5 at even `t` and to 2, 3, 4 at odd `t`; the proximity digraph
is never eventually constant; agents 1, 2, 4, 5 alternate sides of their limits. The tables need the
bounds on the product atom `u φ` (from `1 < φ < 2` and `φ² = φ + 1`); at odd `t` the bound is
`λ ≤ λᵗ`, not only `−1 ≤ λᵗ`.
-/

@[expose] public section

namespace HK

notation "sbi7_N(" S3 ")" =>
  ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, S3, {2, 3, 4, 5}, {3, 4, 5, 6}, {6}]

/-- The SBI-7 table at time `t`. -/
theorem sbi7_closed_form' t :
    tr7i t = aff(sbi7_lim, sbiRate ^ t, fun i => sbi_v i / 2) :=
  traj_eigen (N := fun t => sbi7_N(if Even t then {1, 2, 3, 4, 5} else {2, 3, 4}))

/-- §3: the closed form. -/
theorem sbi7_closed_form t :
    tr7i t = aff(sbi7_lim, sbiRate ^ t / 2, sbi_v) := by
  rw [sbi7_closed_form']; funext i; ring

/-- §3: the neighbourhood table at every `t`. -/
theorem sbi7_neighbors t :
    nbi sbi7_r (tr7i t) =
      sbi7_N(if Even t then {1, 2, 3, 4, 5} else {2, 3, 4}) :=
  nbh sbi7_closed_form'

theorem sbi7_digraph_not_eventually_constant τ :
    ∃ t, τ ≤ t ∧ pdi sbi7_r (tr7i t) ≠ pdi sbi7_r (tr7i τ) :=
  dnec sbi7_neighbors 1

end HK
