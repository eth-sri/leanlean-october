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

local notation "sbc7_N(" S3 ")" =>
  ![{0}, {0, 1, 2}, {1, 2, 3, 4}, S3, {2, 3, 4, 5}, {4, 5, 6}, {6}]

/- The SBC-7 table at time `t`. -/
/-- §2: the closed form. -/
theorem sbc7_closed_form t :
    tr7c t = aff(sbc7_lim, sbcRate ^ t, sbc7_v) :=
  traj_eigen (N := fun t => sbc7_N(if Even t then {3} else {2, 3, 4}))

/-- §2: the neighbourhood table at every `t`. -/
theorem sbc7_neighbors t :
    nbc sbc7_r (tr7c t) =
      sbc7_N(if Even t then {3} else {2, 3, 4}) :=
  nbh sbc7_closed_form

/-- §2: the proximity digraph is never eventually constant (`t = τ + 1` differs from `τ`). -/
theorem sbc7_digraph_not_eventually_constant τ :
    ∃ t, τ ≤ t ∧ pdc sbc7_r (tr7c t) ≠ pdc sbc7_r (tr7c τ) :=
  dnec sbc7_neighbors 2

end HK
