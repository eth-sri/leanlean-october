module

public import HK.SBI7

/-!
# The second 7-agent SBI system (Hegarty–Ognissanti–Wedin §5)

`x(0) = (0, 71, 100 − φ, 110, 120 + φ, 149, 220)`, `r = (85, 35, 35, 75, 35, 35, 85)`,
`λ = (1 − √5)/8`; `x(t) = (0, 70, 100, 110, 120, 150, 220) + λᵗ (0, 1, −φ, 0, φ, −1, 0)`. The
neighbourhood table is the same at every `t`, yet agents 1, 2, 4, 5 alternate sides of their limits;
their per-step convergence factor is `λ` at every `t`. Index 3 (the paper's agent 4) sits at its
limit.
-/

@[expose] public section

namespace HK

/-- §5: the closed form. -/
theorem sbi7b_closed_form t :
    tr7b t = aff(sbi7b_lim, sbiRate ^ t, sbi_v) :=
  traj_eigen (N := fun _ => sbi7_N({2, 3, 4}))

/-- §5: the neighbourhood table, the same at every `t`. -/
theorem sbi7b_neighbors t :
    nbi sbi7b_r (tr7b t) = sbi7_N({2, 3, 4}) :=
  nbh sbi7b_closed_form

theorem sbi7b_fvct t : fvct .sbi sbi7b_r (tr7b t) = sbi7b_lim :=
  fvct_eigen sbi7b_closed_form sbi7b_neighbors

theorem sbi7b_perStepFactor t i (hi : i ∈ ~{1, 2, 4, 5}) :
    perStepFactor .sbi sbi7b_r tr7b i t = sbiRate :=
  perStepFactor_geom sbi7b_closed_form sbi7b_fvct

theorem sbi7b_perStepFactor_not_tendsto i (hi : i ∈ ~{1, 2, 4, 5}) :
    Nlim .sbi sbi7b_r tr7b :=
  ntpsf sbi7b_perStepFactor

theorem sbi7b_digraph_constant t :
    pdi sbi7b_r (tr7b t) = pdi sbi7b_r sbi7b_x0 :=
  digraph_const_of_neighbors sbi7b_neighbors t

end HK
