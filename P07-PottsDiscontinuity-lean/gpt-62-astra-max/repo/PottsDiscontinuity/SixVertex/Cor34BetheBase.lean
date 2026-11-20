module

public import Mathlib
public import PottsDiscontinuity.Bethe.DiscreteBase
public import PottsDiscontinuity.SixVertex.Cor34BetheWave

/-!
# Corollary 3.4: Bethe wave and eigenvalue at infinity

This module specializes the continuous regularizations to the discrete base momentum family.
The parameter `ε` is `1/Δ`; the displayed source limit is always the limit as `ε → 0` from
below when it is interpreted with `Δ < 0`.
-/

@[expose] public section

open Finset Complex Filter Matrix Topology
open scoped BigOperators

namespace PottsDiscontinuity.SixVertex

variable {N n : ℕ} {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n) (hN : 0 < N) (hn : 2 * n ≤ N)

/-- The half-angle root whose square is the source's `ζ=e^(2πi/(N-n))`. -/
noncomputable def cor34_halfRoot (m : ℕ) : ℂ :=
  Complex.exp (Real.pi * I / m)

/-- The discrete base momentum phase is the centered half-root power, including the even
particle-number half-integer shift. -/
theorem cor34_base_z_eq_halfRoot_zpow (hnN : n < N) (j : Fin n) :
    BetheAnsatz.z (Bethe.discreteBaseSolution N n j) =
      cor34_halfRoot (N - n) ^ (2 * j.val + 1 - (n : ℤ)) := by
  have hmNat := Nat.sub_pos_of_lt hnN
  have hp : Bethe.discreteBaseSolution N n j =
      Real.pi * (2 * (j.val : ℤ) + 1 - (n : ℤ) : ℤ) /
        (N - n : ℕ) := by
    dsimp [Bethe.discreteBaseSolution, Bethe.discreteBetheIndex]
    push_cast
    ring
  have harg : I * (Bethe.discreteBaseSolution N n j) =
      (2 * (j.val : ℤ) + 1 - (n : ℤ) : ℤ) *
        (Real.pi * I / (N - n : ℕ)) := by
    rw [hp]
    push_cast
    grind
  unfold BetheAnsatz.z cor34_halfRoot
  rw [harg, Complex.exp_int_mul]

end PottsDiscontinuity.SixVertex
