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

@[expose] public section

namespace HK

local notation "sbc6_N" =>
  ![{0}, {0, 1, 2}, {0, 1, 2, 3}, {2, 3, 4, 5}, {3, 4, 5}, {5}]

/-- §4: the closed form. -/
theorem sbc6_closed_form t :
    tr6c t = aff(sbc6_lim, sbcRate ^ t, sbc6_v) :=
  traj_eigen (N := fun _ => sbc6_N)

/-- §4: the neighbourhood table, the same at every `t`. -/
theorem sbc6_neighbors t :
    nbc sbc6_r (tr6c t) = sbc6_N := nbh sbc6_closed_form

theorem sbc6_digraph_constant t :
    pdc sbc6_r (tr6c t) = pdc sbc6_r sbc6_x0 :=
  digraph_const_of_neighbors sbc6_neighbors t

theorem sbc6_fvct t : fvct .sbc sbc6_r (tr6c t) = sbc6_lim :=
  fvct_eigen sbc6_closed_form sbc6_neighbors

theorem sbc6_perStepFactor t i (hi : i ∈ ~{1, 2, 3, 4}) :
    perStepFactor .sbc sbc6_r tr6c i t = -1 / 6 :=
  perStepFactor_geom sbc6_closed_form sbc6_fvct

theorem sbc6_perStepFactor_not_tendsto i (hi : i ∈ ~{1, 2, 3, 4}) :
    Nlim .sbc sbc6_r tr6c :=
  ntpsf sbc6_perStepFactor

end HK
