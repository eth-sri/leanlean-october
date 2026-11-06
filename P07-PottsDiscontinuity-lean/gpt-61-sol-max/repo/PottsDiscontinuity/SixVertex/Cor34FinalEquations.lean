module

public import Mathlib
public import PottsDiscontinuity.Bethe.DiscreteCore
public import PottsDiscontinuity.BetheAnsatz.Defs

/-! # Corollary 3.4: transfer the discrete Bethe data to Theorem 3.1 -/

@[expose] public section

open Complex

namespace PottsDiscontinuity.SixVertex

/-- The centered quantum number in (BE_Δ) contributes the phase `(-1)^(n-1)` in (BE). -/
theorem cor34_discreteBethe_phase (n : ℕ) (j : Fin n) :
    Complex.exp (I * ((2 * Real.pi *
      Bethe.discreteBetheIndex n j : ℝ) : ℂ)) = (-1 : ℂ) ^ (n - 1) := by
  have hn  := Nat.zero_lt_of_lt j.isLt
  have hindex :
      2 * Real.pi * Bethe.discreteBetheIndex n j =
        (2 *  j.val  - ( n  - 1)) * Real.pi := by
    unfold Bethe.discreteBetheIndex
    ring
  have harg : I *  (2 * Real.pi * Bethe.discreteBetheIndex n j : ℝ)  =
       j.val  * (2 * Real.pi * I) +
         (n - 1 : ℕ)  *  -(Real.pi * I)  := by
    simp_all <;> grind
  have hperiod : Complex.exp ( j.val  * (2 * Real.pi * I)) = 1 := by
    simp_all
  have hsign : Complex.exp ( (n - 1 : ℕ)  *  -(Real.pi * I) ) =
      (-1 ) ^ (n - 1) := by
    rw [Complex.exp_nat_mul]
    all_goals simp_all
  rw [harg, Complex.exp_add, hperiod, hsign, one_mul]

/-- Every solution of the discrete equations with centered indices satisfies the Bethe
equations used by Theorem 3.1. -/
theorem cor34_discreteBetheEquation_to_betheEquations
    {Δ : ℝ} {N n : ℕ} (p : Fin n → ℝ)
    (hBE : Bethe.DiscreteBetheEquation Δ N n p) :
    BetheAnsatz.BetheEquations N Δ p := by
  intro j
  
  calc
    Complex.exp (I *  N  *  p j ) =
        Complex.exp (I *  ( N  * p j : ℝ) ) := by
          
          push_cast
          ring
    _ = Complex.exp (I *
         (2 * Real.pi * Bethe.discreteBetheIndex n j -
          ∑ k : Fin n, Bethe.theta Δ (p j) (p k) : ℝ) ) := by
          rw [hBE j]
    _ = Complex.exp (I *  (2 * Real.pi * Bethe.discreteBetheIndex n j : ℝ) ) *
        Complex.exp (- (I *   ∑ k : Fin n, Bethe.theta Δ (p j) (p k)  )) := by
          rw [show I *
               (2 * Real.pi * Bethe.discreteBetheIndex n j -
                ∑ k : Fin n, Bethe.theta Δ (p j) (p k) : ℝ)  =
                I *  (2 * Real.pi * Bethe.discreteBetheIndex n j : ℝ)  +
                  - (I *   ∑ k : Fin n, Bethe.theta Δ (p j) (p k)  ) by
                    push_cast
                    ring,
            Complex.exp_add]
    _ = (-1 ) ^ (n - 1) *
        Complex.exp (- (I *  (∑ k : Fin n, Bethe.theta Δ (p j) (p k) ) )) := by
          rw [ cor34_discreteBethe_phase n j ]

section

variable {n : ℕ} {p : Fin n → ℝ} (hp : p ∈ Bethe.S_n n)
include hp

/-- The strict ordering in `S_n` makes all momenta distinct. -/
theorem cor34_S_n_injective  :
    Function.Injective p :=
  hp.2.1.injective

/-- For even particle number, symmetry and strict ordering exclude a zero momentum. -/
theorem cor34_even_S_n_roots_nonzero  (hn : Even n) (j : Fin n) : p j ≠ 0 := by
  intro hj
  have hrev : Fin.rev j = j := hp.2.1.injective (by rw [hp.2.2 j, hj, neg_zero])
  grind

end

/-- For odd particle number, the fixed middle index is the unique zero momentum. -/
theorem cor34_odd_S_n_center_zero {n q : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ Bethe.S_n n) (hnq : n + 1 = 2 * q) :
    p (⟨q - 1, by omega⟩ : Fin n) = 0 := by
  let l : Fin n := ⟨q - 1, by omega⟩
  have hrev : Fin.rev l = l := by
    apply Fin.ext
    simp [l]
    omega
  have hs := hp.2.2 l
  rw [hrev] at hs
  linarith

end PottsDiscontinuity.SixVertex
