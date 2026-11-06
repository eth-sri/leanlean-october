module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningProfile
import Mathlib.Tactic.Linarith

/-! # Values and plateau of the selected flattened profile -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter

/-- The fixed flattening primitive grows at most linearly on the whole real line. -/
theorem abs_flatteningPsi_le (s : ℝ) : |flatteningPsi s| ≤ |s| := by
  have hb (t : ℝ) : ‖deriv flatteningPsi t‖ ≤ (1) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (flatteningPsi_deriv_bounds t).1]
    exact (flatteningPsi_deriv_bounds t).2
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t (_) =>
      (contDiff_flatteningPsi.differentiable (by simp)) t)
    (fun t _ => hb t) convex_univ (Set.mem_univ (0)) (Set.mem_univ s)
  simpa only [flatteningPsi_eq_zero 0 (by norm_num), sub_zero, one_mul, Real.norm_eq_abs] using h

/-- A scalar bound on the unflattened value gives a uniform bound on its literal flattening. -/
theorem abs_flatProfile_le {d : ℕ} (H : XV d → ℝ) (alpha r : ℝ) (hr : 0 < r)
    (q : XV d) :
    |flatProfile H flatteningPsi flatteningOffset alpha r q| ≤
      1 + |flatteningOffset| * Real.rpow r alpha + |H q| := by
  let a := Real.rpow r alpha
  have hp : 0 < a := Real.rpow_pos_of_pos hr alpha
  have hb := mul_le_mul_of_nonneg_left (abs_flatteningPsi_le (H q / a)) hp.le
  have he : a * |H q / a| = |H q| := by
    grind
  rw [he] at hb
  calc
    _ ≤ |1 - flatteningOffset * a| + |a * flatteningPsi _| := abs_sub _ _
    _ ≤ 1 + |flatteningOffset| * a + |H q| := by
      have hfirst := abs_sub (1) (flatteningOffset * a)
      rw [abs_one, abs_mul, abs_of_pos hp] at hfirst
      grind

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
