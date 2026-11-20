module

public import HK.Basic

/-!
# The 6-agent SBC system (Hegarty–Ognissanti–Wedin §4)

`x(0) = (0, 22, 37, 103, 118, 140)`, `r = (10, 70, 70, 70, 70, 10)`;
`x(t) = (0, 20, 40, 100, 120, 140) + (−1/6)ᵗ (0, 2, −3, 3, −2, 0)`. The neighbourhood table is the
same at every `t` (so the proximity digraph is constant), yet agents 1–4 alternate sides of their
limits; their per-step convergence factor (Definition 6.1, with the final value at constant topology
of Definition 3.1 equal to the limit) is `−1/6` at every `t`.
-/

public section

namespace HK

theorem sbc6Mode : Mode .sbc sbc6_r sbc6_x0 sbc6_lim sbc6_v sbcRate
    (fun _ => rows![{0}, 0⋯2, 0⋯3, 2⋯5, 3⋯5, {5}]) := by certify

corollary sbc6_closed_form := sbc6Mode.form

corollary sbc6_neighbors := sbc6Mode.orbit.table

corollary sbc6_digraph_constant := sbc6Mode.orbit.constant

corollary sbc6_fvct := sbc6Mode.final

corollary sbc6_perStepFactor := sbc6Mode.factor 1⋯4

corollary sbc6_perStepFactor_not_tendsto := sbc6Mode.noFactorLimit _ sbc6_perStepFactor

end HK
