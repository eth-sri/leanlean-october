module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SurvivalKernel
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! # Iterating a uniform half-mass time

These internal kernel lemmas retain their literal uniform hypothesis. The active
survival theorem discharges it using the quadratic occupation calculation.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous



variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H) (hE : IsStripEvolution A H E) (D : ℝ) (hD : 0 < D) (hhalf : ∀ s z, stripSurvivingMass H E s (s + D) (le_add_of_nonneg_right hD.le) z ≤ 1 / 2)

include hE hhalf
/-- A uniform half-mass estimate iterates through actual killed-kernel composition. -/
theorem stripSurvivingMass_geometric_of_half_mass
    (s : ℝ) (z : EvolutionState (intervalDomain H) (fun _ => 0) s) (n : ℕ) :
    stripSurvivingMass H E s (s + n * D)
      (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hD.le)) z ≤
        (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero =>
    simpa only [Nat.cast_zero, zero_mul, add_zero, pow_zero] using
      (stripSurvivingMass_bounds A H E hE s s le_rfl z).2
  | succ n ih =>

    have htu : s + n * D ≤ s + (n + 1 : ℕ) * D := by
      rw [Nat.cast_add, Nat.cast_one, add_mul]
      linarith


    have hm := stripSurvivingMass_le_mul_of_later_bound A H E hE s
      (s + n * D) _ (1 / 2) (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hD.le)) htu (by
          intro w
          have hs := hhalf (s + n * D) w
          change E.1 (s + n * D) ((s + n * D) + D) _ 1 w ≤ 1 / 2 at hs
          have heq : E.1 (s + n * D) _ htu 1 w =
              E.1 (s + n * D) _ (le_add_of_nonneg_right hD.le) 1 w := by
            exact congrArg (fun u : {u : ℝ // s + n * D ≤ u} =>
              E.1 (s + n * D) u.1 u.2 1 w)
              (show (⟨_, htu⟩ : {u : ℝ // s + n * D ≤ u}) =
                ⟨(s + n * D) + D, le_add_of_nonneg_right hD.le⟩ from Subtype.ext (by
                    push_cast
                    ring))
          rw [heq]
          exact hs) z
    exact hm.trans (by simpa only [pow_succ, mul_comm] using
      mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 1 / 2))

/-- A geometric bound at half-mass times gives the source exponential estimate at every time. -/
theorem stripSurvivingMass_exp_of_half_mass
    (s t : ℝ) (ht : 0 ≤ t)
    (z : EvolutionState (intervalDomain H) (fun _ => 0) s) :
    stripSurvivingMass H E s (s + t) (le_add_of_nonneg_right ht) z ≤
      2 * Real.exp (-Real.log 2 * t / D) := by
  let sharedTerm_89459cf4f8 := (Real.exp_log (by norm_num : (0 : ℝ) < 2))
  let n := Nat.floor (t / D)

  have hn'  := Nat.lt_floor_add_one (t / D)
  have htime  := add_le_add_right ((le_div_iff₀ hD).mp (Nat.floor_le (div_nonneg ht hD.le))) s
  have hm := stripSurvivingMass_antitone A H E hE s (s + n * D) (s + t)
    (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hD.le)) htime z




  calc
    _ ≤ (1 / 2 : ℝ) ^ n := hm.trans (stripSurvivingMass_geometric_of_half_mass A H E hE D hD hhalf s z n)
    _ = Real.exp (-Real.log 2 * n) := (by
        rw [mul_comm (-Real.log 2) (n : ℝ), Real.exp_nat_mul,
          Real.exp_neg, sharedTerm_89459cf4f8]
        simp only [one_div])
    _ ≤ Real.exp (Real.log 2 + (-Real.log 2 * t / D)) := Real.exp_le_exp.mpr (by
        have hh := mul_le_mul_of_nonneg_left hn'.le (show 0 < Real.log (2 ) from Real.log_pos (by norm_num)).le
        have heq : Real.log 2 * (t / D) = Real.log 2 * t / D := by ring
        rw [heq] at hh
        rw [mul_add, mul_one] at hh
        rw [neg_mul, neg_mul, neg_div]
        linarith only [hh])
    _ = 2 * Real.exp (-Real.log 2 * t / D) := by
      rw [Real.exp_add, sharedTerm_89459cf4f8]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
