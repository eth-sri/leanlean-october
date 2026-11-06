module

public import Mathlib
public import PottsDiscontinuity.Bethe.DiscreteCore

/-!
# The discrete Bethe equations at `Δ = -∞`

At the inverse parameter `ε=0`, the phase is `Θ(x,y)=y-x`.  This file proves
the explicit solution and uniqueness of the resulting finite system.
-/

@[expose] public section

open scoped BigOperators

namespace PottsDiscontinuity.Bethe

/-- A symmetric vector has total sum zero. -/
theorem sum_eq_zero_of_mem_R_n_sym {n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ R_n_sym n) : (∑ j : Fin n, p j) = 0 := by
  have hs : (∑ j : Fin n, p j) = -(∑ j : Fin n, p j) := by
    calc
      (∑ j : Fin n, p j) = ∑ j : Fin n, p (Fin.rev j) :=
        (Equiv.sum_comp Fin.revPerm _).symm
      _ = ∑ j : Fin n, -p j := by
        apply Finset.sum_congr rfl
        tauto
      _ = -(∑ j : Fin n, p j) := by simp
  linarith

section
variable (N n : ℕ)
/-- The limiting Bethe equations obtained by setting `Θ(x,y)=y-x`. -/
def DiscreteBetheEquationAtInfinity (p : Fin n → ℝ) : Prop :=
  ∀ j, (N : ℝ) * p j =
    2 * Real.pi * discreteBetheIndex n j - ∑ k : Fin n, (p k - p j)

/-- Explicit solution at `Δ=-∞`: `p_j=2πI_j/(N-n)`. -/
noncomputable def discreteBaseSolution  : Fin n → ℝ :=
  fun j => 2 * Real.pi * discreteBetheIndex n j / ((N - n : ℕ) : ℝ)
end

section
variable {N n : ℕ}
theorem baseDenom_pos (hN : 0 < N) (hn : 2 * n ≤ N) :
    0 < ((N - n : ℕ) : ℝ) := by
  have hlt : n < N := by omega
  simp_all

theorem baseDenom_ge_n (hn : 2 * n ≤ N) :
    (n : ℝ) ≤ ((N - n : ℕ) : ℝ) := by
  have hnat : n ≤ N - n := by omega
  simp_all
end

theorem discreteBetheIndex_abs_bound (n : ℕ) (j : Fin n) :
    |discreteBetheIndex n j| ≤ ((n : ℝ) - 1) / 2 := by
  have hj1 : (j.val : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt j.isLt)
  grind [discreteBetheIndex]

section
variable {N n : ℕ} (hN : 0 < N) (hn : 2 * n ≤ N)
include hN hn
/-- The explicit limiting solution belongs to the ordered symmetric configuration space. -/
theorem discreteBaseSolution_mem_S_n  :
    discreteBaseSolution N n ∈ S_n n := by
  have hD := baseDenom_pos hN hn
  have hDge := baseDenom_ge_n hn
  constructor
  · intro j
    have hI := discreteBetheIndex_abs_bound n j
    have hI2 : 2 * |discreteBetheIndex n j| < ((N - n : ℕ) : ℝ) := by
      nlinarith
    have hnum : 2 * Real.pi * |discreteBetheIndex n j| <
        Real.pi * ((N - n : ℕ) : ℝ) := by
      nlinarith [mul_lt_mul_of_pos_left hI2 Real.pi_pos]
    have habs :
        |2 * Real.pi * discreteBetheIndex n j / ((N - n : ℕ) : ℝ)| =
          (2 * Real.pi * |discreteBetheIndex n j|) / ((N - n : ℕ) : ℝ) := by
      rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi), abs_of_pos hD]
    have hlt :
        |2 * Real.pi * discreteBetheIndex n j / ((N - n : ℕ) : ℝ)| < Real.pi := by
      rw [habs]
      exact (div_lt_iff₀ hD).2 hnum
    grind [discreteBaseSolution]
  constructor
  · intro i j hij
    have hI : discreteBetheIndex n i < discreteBetheIndex n j := by
      simp_all [discreteBetheIndex]
    apply (div_lt_div_iff₀ hD hD).2
    have hnum : 2 * Real.pi * discreteBetheIndex n i <
        2 * Real.pi * discreteBetheIndex n j :=
      mul_lt_mul_of_pos_left hI (by positivity)
    simp_all
  · intro j
    simp only [discreteBaseSolution, discreteBetheIndex_rev]
    ring

/-- The explicit vector is a solution of the limiting equations. -/
theorem discreteBaseSolution_solves_at_infinity  :
    DiscreteBetheEquationAtInfinity N n (discreteBaseSolution N n) := by
  have hDpos := baseDenom_pos hN hn
  have hpSym : discreteBaseSolution N n ∈ R_n_sym n := by
    intro j
    simp only [discreteBaseSolution, discreteBetheIndex_rev]
    ring
  have hpsum := sum_eq_zero_of_mem_R_n_sym hpSym
  have hNdecomp : (N : ℝ) = ((N - n : ℕ) : ℝ) + (n : ℝ) := by
    have hnat : N - n + n = N := by omega
    exact_mod_cast hnat.symm
  have hgap (j : Fin n) :
      (∑ k : Fin n, (discreteBaseSolution N n k - discreteBaseSolution N n j)) =
        -(n : ℝ) * discreteBaseSolution N n j := by
    simp_all
  intro j
  grind [discreteBaseSolution]
end

end PottsDiscontinuity.Bethe
