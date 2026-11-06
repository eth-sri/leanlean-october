module

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.Product

public section

@[expose] section

namespace OAI

/-!
# The scalar simultaneous induction in Section 6

The two diagonal inequalities imply, simultaneously, lower bounds for the
limiting row slopes and for the diagonal profile.  All profile properties
needed for this argument are expressed as hypotheses below.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- One step of the Section 6 simultaneous induction, with a positive real
index. The proof uses the diagonal increment inequality to obtain the second
conclusion as well as the first. -/
theorem growthRecurrence_step_real
    {n Dprev Dnext gprev gnext Gprev : ℝ} (hn : 0 < n)
    (hupper : Dnext ≤ ((3 * (n + 1) - 1) / 2) * gnext)
    (hincrement : Dprev + gprev + gnext ≤ Dnext)
    (hgprev : Gprev ≤ gprev)
    (hDprev : ((3 * n - 1) / 2) * Gprev ≤ Dprev) :
    (1 + 1 / (3 * n)) * Gprev ≤ gnext ∧
      ((3 * (n + 1) - 1) / 2) * ((1 + 1 / (3 * n)) * Gprev) ≤ Dnext := by
  constructor <;> field_simp [ne_of_gt hn] at * <;> nlinarith

/-- The natural-number form of the scalar induction step, indexed by `n + 1`
so that no truncated subtraction occurs in the recurrence. -/
theorem growthRecurrence_step
    {n : ℕ} (hn : 1 ≤ n) {Dprev Dnext gprev gnext Gprev : ℝ}
    (hupper : Dnext ≤ ((3 * ((n : ℝ) + 1) - 1) / 2) * gnext)
    (hincrement : Dprev + gprev + gnext ≤ Dnext)
    (hgprev : Gprev ≤ gprev)
    (hDprev : ((3 * (n : ℝ) - 1) / 2) * Gprev ≤ Dprev) :
    (1 + 1 / (3 * (n : ℝ))) * Gprev ≤ gnext ∧
      ((3 * ((n : ℝ) + 1) - 1) / 2) *
        ((1 + 1 / (3 * (n : ℝ))) * Gprev) ≤ Dnext :=
  growthRecurrence_step_real (by exact_mod_cast (show 0 < n by omega))
    hupper hincrement hgprev hDprev

/-- A zero-indexed version of `growthRecurrence_induction`, convenient when the
initial term of the comparison sequence is stored at index zero. -/
theorem growthRecurrence_induction_shifted
    (D g H : ℕ → ℝ)
    (hHbase : H 0 = 1)
    (hgbase : 1 ≤ g 1)
    (hDbase : 1 ≤ D 1)
    (hHstep : ∀ n : ℕ,
      H (n + 1) = (1 + 1 / (3 * ((n : ℝ) + 1))) * H n)
    (hupper : ∀ n : ℕ, 1 ≤ n →
      D n ≤ ((3 * (n : ℝ) - 1) / 2) * g n)
    (hincrement : ∀ n : ℕ, 1 ≤ n →
      D n + g n + g (n + 1) ≤ D (n + 1)) :
    ∀ n : ℕ, H n ≤ g (n + 1) ∧
      ((3 * ((n : ℝ) + 1) - 1) / 2) * H n ≤ D (n + 1) := by
  intro n
  induction n with
  | zero =>
      norm_num [hHbase]
      exact ⟨hgbase, hDbase⟩
  | succ n ih =>
      have hn : 1 ≤ n + 1 := by omega
      have hu : D (n + 1 + 1) ≤
          ((3 * (((n + 1 : ℕ) : ℝ) + 1) - 1) / 2) * g (n + 1 + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          hupper (n + 1 + 1) (by omega)
      have hp : ((3 * ((n + 1 : ℕ) : ℝ) - 1) / 2) * H n ≤ D (n + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using ih.2
      have hs := growthRecurrence_step hn hu (hincrement (n + 1) hn) ih.1 hp
      simpa only [hHstep, Nat.cast_add, Nat.cast_one] using hs

/-- Combining the scalar induction with the elementary product estimate gives
an exact fourth-power lower bound on the cube of each diagonal value. -/
theorem diagonal_fourth_power_lower
    (D g : ℕ → ℝ)
    (hgbase : 1 ≤ g 1)
    (hDbase : 1 ≤ D 1)
    (hupper : ∀ n : ℕ, 1 ≤ n →
      D n ≤ ((3 * (n : ℝ) - 1) / 2) * g n)
    (hincrement : ∀ n : ℕ, 1 ≤ n →
      D n + g n + g (n + 1) ≤ D (n + 1))
    (n : ℕ) :
    ((n : ℝ) + 1) ^ 4 ≤ D (n + 1) ^ 3 := by
  have hdiag := (growthRecurrence_induction_shifted D g growthProduct
    growthProduct_zero hgbase hDbase
    (fun n => by rw [growthProduct_succ, mul_comm]) hupper hincrement n).2
  have hpositive := growthProduct_pos n
  have hlinear : ((n : ℝ) + 1) * growthProduct n ≤ D (n + 1) := by
    have hcoeff : (n : ℝ) + 1 ≤ (3 * ((n : ℝ) + 1) - 1) / 2 := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact (mul_le_mul_of_nonneg_right hcoeff (le_of_lt hpositive)).trans hdiag
  calc
    ((n : ℝ) + 1) ^ 4 = ((n : ℝ) + 1) ^ 3 * ((n : ℝ) + 1) := by ring
    _ ≤ ((n : ℝ) + 1) ^ 3 * growthProduct n ^ 3 :=
      mul_le_mul_of_nonneg_left (growthProduct_cube_lower n) (by positivity)
    _ = (((n : ℝ) + 1) * growthProduct n) ^ 3 := by ring
    _ ≤ D (n + 1) ^ 3 := pow_le_pow_left₀ (by positivity) hlinear 3

/-- The diagonal fourth-power lower bound using the paper's positive indices. -/
theorem diagonal_fourth_power_lower_of_one_le
    (D g : ℕ → ℝ)
    (hgbase : 1 ≤ g 1)
    (hDbase : 1 ≤ D 1)
    (hupper : ∀ n : ℕ, 1 ≤ n →
      D n ≤ ((3 * (n : ℝ) - 1) / 2) * g n)
    (hincrement : ∀ n : ℕ, 1 ≤ n →
      D n + g n + g (n + 1) ≤ D (n + 1))
    (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) ^ 4 ≤ D n ^ 3 := by
  cases n with
  | zero => omega
  | succ n =>
      simpa only [Nat.cast_add, Nat.cast_one] using
        diagonal_fourth_power_lower D g hgbase hDbase hupper hincrement n

end MatrixMultiplication.AuxiliarySeparation

end OAI
