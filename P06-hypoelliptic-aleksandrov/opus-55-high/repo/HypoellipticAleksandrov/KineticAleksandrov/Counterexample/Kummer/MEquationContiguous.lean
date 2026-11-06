module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MEquation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Contiguous relations for the literal Kummer series

These identities raise the first parameter while preserving positive Euler endpoint parameters.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

variable (a : ℝ) (b : Pos) (n : ℕ)

/-- Compatibility of the two rising-factorial recurrences. -/
theorem poch_shift  :
    a * poch (a + 1) n = (a + n) * poch a n := by
  rw [← poch_succ_left, poch_succ, mul_comm]

/-- The coefficient identity underlying the positive-parameter continuation. -/
theorem coeff_contiguous_succ  :
    coeff a b (n + 1) = coeff (a + 1) (next b) (n + 1) +
      ((a - b.1) / (b.1 * (b.1 + 1))) * coeff (a + 1) (next (next b)) n := by
  have hb := ne_of_gt b.2
  have hb1 : b.1 + 1 ≠ 0 := ne_of_gt (next b).2
  have hp1 := ne_of_gt (poch_pos (next b) n)
  have hp2 := ne_of_gt (poch_pos (next (next b)) n)
  have hs := poch_shift (b.1 + 1) n
  change (b.1 + 1) * poch (next (next b)).1 n =
    (b.1 + 1 + n) * poch (next b).1 n at hs
  simp only [coeff, poch_succ (a + 1),
    poch_succ_left,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  change a * poch _ n / (b.1 * poch (next b).1 n * ((n + 1) * n.factorial)) =
    poch _ n * (a + 1 + n) /
      ((b.1 + 1) * poch (next _).1 n * ((n + 1) * n.factorial)) +
      (a - b.1) / (b.1 * (b.1 + 1)) *
        (poch _ n / (poch _ n * n.factorial))
  field_simp
  grind

/-- A contiguous relation expressing all admissible parameters through positive Euler ones. -/
theorem M_contiguous  (z : ℝ) :
    M a b z = M (a + 1) (next b) z +
      ((a - b.1) * z / (b.1 * (b.1 + 1))) * M (a + 1) (next (next b)) z := by
  have hs := (hasSum_M (a + 1) (next (next b)) z).mul_left
    ((a - b.1) * z / (b.1 * (b.1 + 1)))
  have he (n : ℕ) :
      ((a - b.1) * z / (b.1 * (b.1 + 1))) *
        (coeff (a + 1) (next (next b)) n * z ^ n) =
      ((a - b.1) / (b.1 * (b.1 + 1))) *
        coeff (a + 1) (next (next b)) n * z ^ (n + 1) := by
    ring
  simp only [he] at hs
  let f  := fun n => (coeff a b n - coeff (a + 1) (next b) n) * z ^ n
  have hf (n : ℕ) : f (n + 1) =
      ((a - b.1) / (b.1 * (b.1 + 1))) *
        coeff (a + 1) (next (next b)) n * z ^ (n + 1) := by
    dsimp [f]
    rw [coeff_contiguous_succ]
    ring
  have hsum : HasSum f
      (((a - b.1) * z / (b.1 * (b.1 + 1))) * M (a + 1) (next (next b)) z) := by
    have h0 : f 0 = 0 := by simp [f]
    simpa only [h0, zero_add] using (hs.congr_fun (fun n => hf n)).zero_add (f := f)
  have hdiff := (hasSum_M a b z).sub (hasSum_M (a + 1) (next b) z)
  have hdiff' : HasSum f (M a b z - M (a + 1) (next b) z) := by
    grind
  have h := hdiff'.unique hsum
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
