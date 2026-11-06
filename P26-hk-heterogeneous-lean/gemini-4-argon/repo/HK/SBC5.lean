module

public import HK.Basic

/-!
# Five SBC agents with a constant digraph and oscillating convergence (this development)

`x(0) = (0, 7, 12 − √2, 19, 24)`, `r = (3, 9, 9, 9, 3)`;
`x(t) = (0, 6, 12, 18, 24) + ((1 − √2)/3)ᵗ (0, 1, −√2, 1, 0)`. The neighbourhood table
`{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}` is the same at every `t`, yet agents 1, 2, 3 alternate sides
of their limits. Hence Theorem 6.4(iv) and Conjecture 2.3 fail already with five SBC agents. The
identities used: `√2² = 2`; `3λ − 1 = −√2`; `λ√2 = (√2 − 2)/3`; the rate lies in `(−1/6, 0)`
(`1.4 < √2 < 1.5`), so `λ ≤ λᵗ ≤ 1` for every `t` and one table serves both parities.
-/

@[expose] public section

namespace HK

open Filter Topology

set_option hygiene false

local notation "sbc5_N" =>
  ![{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}]
local notation "trf" => traj .sbc (sbc5Family_r δ) (sbc5Family_x0 δ)
local notation "u" => sbc5Rate ^ t

variable (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
include hδ0 hδ1

/-- The five-agent family table at time `t`. -/
theorem sbc5Family_table t :
    nbc (sbc5Family_r δ) (aff(sbc5_lim, u, fun i => δ * sbc5_v i)) = sbc5_N := by
  have := sbc_sqrt_two_bounds
  have := neg_pow_bounds sbc5Rate_lt t
  have : -δ ≤ u * δ := by nlinarith [sbc5Rate_lt]
  have : u * δ ≤ δ := by nlinarith
  have : -2 * δ ≤ u * (δ * Real.sqrt 2) := by nlinarith
  have : u * (δ * Real.sqrt 2) ≤ 2 * δ := by nlinarith
  hk_table

theorem sbc5Family_closed_form' t :
    trf t = aff(sbc5_lim, u, fun i => δ * sbc5_v i) :=
  traj_eigen (sbc5Family_table δ hδ0 hδ1)

theorem sbc5Family_closed_form t :
    trf t = aff(sbc5_lim, u * δ, sbc5_v) := by
  rw [sbc5Family_closed_form' δ hδ0 hδ1]; funext i; ring

theorem sbc5Family_neighbors t :
    nbc (sbc5Family_r δ) (trf t) = sbc5_N := by
  rw [sbc5Family_closed_form' δ hδ0 hδ1, sbc5Family_table δ hδ0 hδ1]

omit hδ0 hδ1

theorem sbc5_eq_family : sbc5_r = sbc5Family_r 1 ∧ sbc5_x0 = sbc5Family_x0 1 := by
  constructor <;> funext i <;> fin_cases i <;> simp <;> ring

local notation "fam1" f => by rw [sbc5_eq_family.1, sbc5_eq_family.2]; simpa using f 1 zero_lt_one le_rfl t

theorem sbc5_closed_form t :
    tr5 t = aff(sbc5_lim, u, sbc5_v) := fam1 sbc5Family_closed_form

theorem sbc5_neighbors t :
    nbc sbc5_r (tr5 t) = sbc5_N := fam1 sbc5Family_neighbors

/-- The final value at constant topology along the trajectory is the limit at every `t`. -/
theorem sbc5_fvct t : fvct .sbc sbc5_r (tr5 t) = sbc5_lim :=
  fvct_eigen sbc5_closed_form sbc5_neighbors

/-- The per-step convergence factor of agents 1, 2, 3 is `λ` at every `t`. -/
theorem sbc5_perStepFactor t i (hi : i ∈ ~{1, 2, 3}) :
    perStepFactor .sbc sbc5_r tr5 i t = sbc5Rate :=
  perStepFactor_geom sbc5_closed_form sbc5_fvct

local notation "trx" => traj .sbc r x₀

/-- No positive bound on relative radius spread restores eventual pseudo-stability, even
for a constant-digraph SBC system on five agents. The pairwise inequalities express that
the largest radius divided by the smallest is strictly below `1+ε`. -/
theorem sbc5_near_homogeneous ε (hε : 0 < ε) :
    ∃ r x₀ : V 5,
      (∀ i, 0 < r i) ∧
      (∀ i j, r i < (1 + ε) * r j) ∧
      r 0 < r 1 ∧
      (∀ t, pdc r (trx t) = pdc r x₀) ∧
      Tendsto trx atTop (𝓝 sbc5_lim) ∧
      (∀ τ, ¬ FixedFrom trx τ) ∧
      (∀ xinf τ, ¬ PseudoStableAfter trx xinf τ) := by
  let δ := min (1 / 2) (ε / 4)
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have : δ ≤ 1 / 2 ∧ δ ≤ ε / 4 := ⟨min_le_left _ _, min_le_right _ _⟩
  have hx := sbc5Family_closed_form' δ hδ0 (by linarith)
  exact ⟨sbc5Family_r δ, sbc5Family_x0 δ,
    fun i => by fin_cases i <;> simp <;> linarith,
    fun i j => by fin_cases i <;> fin_cases j <;> simp <;> nlinarith,
    by simp; linarith,
    digraph_const_of_neighbors (sbc5Family_neighbors δ hδ0 (by linarith)),
    tendsto_geom hx,
    fun _ => not_fixedFrom_geom hx (hv := by simp [hδ0.ne']),
    fun _ _ => not_pseudoStable_geom hx⟩

end HK
