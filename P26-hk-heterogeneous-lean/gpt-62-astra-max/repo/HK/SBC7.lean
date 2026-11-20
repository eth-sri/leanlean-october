module

public import HK.Basic

/-!
# The 7-agent SBC system (Hegarty–Ognissanti–Wedin §2)

`x(0) = (0, 38, 69, 84, 99, 130, 168)`, `r = (18, 42, 48, 12, 48, 42, 18)`;
`x(t) = (0, 36, 72, 84, 96, 132, 168) + (−1/6)ᵗ (0, 2, −3, 0, 3, −2, 0)`. The middle agent (index 3)
listens to itself alone at even `t` and to indices 2, 3, 4 at odd `t`; the proximity digraph is
never eventually constant; agents 1, 2, 4, 5 alternate sides of their limits.
-/

public section

namespace HK

theorem sbc7Mode : Mode .sbc sbc7_r sbc7_x0 sbc7_lim sbc7_v sbcRate
    (fun t => rows![{0}, 0⋯2, 1⋯4, if Even t then {3} else 2⋯4, 2⋯5, 4⋯6, {6}]) := by certify

corollary sbc7_closed_form := sbc7Mode.form

corollary sbc7_neighbors := sbc7Mode.orbit.table

corollary sbc7_digraph_not_eventually_constant := sbc7Mode.orbit.changes

end HK
