module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MAsymptoticsPositive
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Continuation of the negative-axis expansion

A proved contiguous relation raises the first parameter above zero without changing the theorem.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open Filter Asymptotics

variable (a : ℝ) (b : Pos)

/-- The second contiguous coefficient after Gamma cancellation. -/
theorem expansionCoeff_contiguous_second  (hab : a < b.1) (n : ℕ) :
    -((a - b.1) / (b.1 * (b.1 + 1))) *
      expansionCoeff (a + 1) (b.1 + 2) n =
      Real.Gamma b.1 / Real.Gamma (b.1 - a) *
        poch (a + 1) n * poch (a - b.1) n / (n.factorial : ℝ) := by
  have hb := ne_of_gt b.2
  have hb1 : b.1 + 1 ≠ 0 := ne_of_gt (next b).2
  have hc := ne_of_gt (sub_pos.mpr hab)
  rw [expansionCoeff, show b.1 + 2 = (b.1 + 1) + 1 by ring,
    Real.Gamma_add_one hb1, Real.Gamma_add_one hb,
    show (b.1 + 1 + 1) - (a + 1) = (b.1 - a) + 1 by ring,
    Real.Gamma_add_one hc]
  grind

/-- The constant coefficient of the contiguous expansion. -/
theorem expansionCoeff_contiguous_zero  (hab : a < b.1) :
    expansionCoeff a b.1 0 = -((a - b.1) / (b.1 * (b.1 + 1))) *
      expansionCoeff (a + 1) (b.1 + 2) 0 := by
  rw [expansionCoeff_contiguous_second a b hab]
  simp only [expansionCoeff, poch_zero]

/-- The higher coefficients of the contiguous expansion. -/
theorem expansionCoeff_contiguous_succ  (hab : a < b.1) (n : ℕ) :
    expansionCoeff a b.1 (n + 1) = expansionCoeff (a + 1) (b.1 + 1) n +
      -((a - b.1) / (b.1 * (b.1 + 1))) *
        expansionCoeff (a + 1) (b.1 + 2) (n + 1) := by
  rw [expansionCoeff_contiguous_second a b hab, expansionCoeff, expansionCoeff,
    Real.Gamma_add_one (ne_of_gt b.2),
    poch_succ_left a n, poch_succ (a - b.1 + 1) n,
    poch_succ (a + 1) n, poch_succ_left (a - b.1) n,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]
  field_simp
  ring

/-- The exact matching of finite contiguous expansions at adjacent truncation orders. -/
theorem mExpansion_contiguous  (hab : a < b.1) (N : ℕ)
    (X : ℝ) (hX : 0 < X) :
    mExpansion a b.1 (N + 1) X = mExpansion (a + 1) (b.1 + 1) N X +
      (-((a - b.1) / (b.1 * (b.1 + 1))) * X) *
        mExpansion (a + 1) (b.1 + 2) (N + 1) X := by
  rw [mExpansion_eq_sum a b.1 _ X hX,
    mExpansion_eq_sum _ _ N X hX,
    mExpansion_eq_sum _ _ _ X hX]
  let k  := -((a - b.1) / (b.1 * (b.1 + 1)))
  have hx (n : ℕ) : X * Real.rpow X (-(a + 1 + n)) = Real.rpow X (-(a + n)) := by
    change X * X ^ (-(a + 1 + n)) = X ^ (-(a + n))
    calc
      _ = X ^ (1) * X ^ (-(a + 1 + n)) := by simp
      _ = X ^ ((1) + -(a + 1 + n)) := (Real.rpow_add hX _ _).symm
      _ = _ := by ring
  have hm : (k * X) *
      (∑ n ∈ Finset.range (N + 1), expansionCoeff (a + 1) (b.1 + 2) n *
        Real.rpow X (-(a + 1 + n))) =
      ∑ n ∈ Finset.range (N + 1), k * expansionCoeff (a + 1) (b.1 + 2) n *
        Real.rpow X (-(a + n)) := by
    rw [Finset.mul_sum]
    grind
  rw [hm]
  have ht (n : ℕ) : expansionCoeff a b.1 (n + 1) *
      Real.rpow X (-(a + (n + 1 : ℕ))) =
      expansionCoeff (a + 1) (b.1 + 1) n * Real.rpow X (-(a + 1 + n)) +
      k * expansionCoeff (a + 1) (b.1 + 2) (n + 1) *
        Real.rpow X (-(a + (n + 1 : ℕ))) := by
    rw [expansionCoeff_contiguous_succ a b hab]
    grind
  have hs := Finset.sum_congr (s₁ := Finset.range N) rfl (fun n _ => ht n)
  rw [Finset.sum_add_distrib] at hs
  simp only [Finset.sum_range_succ']
  rw [expansionCoeff_contiguous_zero a b hab]
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
