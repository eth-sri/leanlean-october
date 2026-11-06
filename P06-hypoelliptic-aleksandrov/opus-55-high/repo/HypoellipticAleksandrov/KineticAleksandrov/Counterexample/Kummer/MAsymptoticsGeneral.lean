module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MAsymptoticsContinuation
import Mathlib.Tactic.Ring

/-!
# General negative-axis expansion

The proved contiguous relation extends Euler asymptotics to every first parameter above minus one.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open Filter Asymptotics

/-- Monotonicity of algebraic asymptotic orders on the positive half-line. -/
theorem rpow_isBigO_of_le (r s : ℝ) (hrs : r ≤ s) :
    IsBigO atTop (fun X : ℝ => X ^ r) (fun X => X ^ s) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (1)] with X hX
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _), one_mul]
  exact Real.rpow_le_rpow_of_exponent_le hX hrs

variable (a : ℝ) (b : Pos)

/-- Continuation gives the expansion at every positive truncation order. -/
theorem M_negative_expansion_succ 
    (ha : -1 < a) (hab : a < b.1) (N : ℕ) :
    IsBigO atTop (fun X => M a b (-X) - mExpansion a b.1 (N + 1) X)
      (fun X => X ^ (-a - ((N + 1 : ℕ) : ℝ))) := by
  have ha1 : 0 < a + 1 := by linarith
  have hab1 : a + 1 < (next b).1 := by change a + 1 < b.1 + 1; simp_all
  have hab2 : a + 1 < (next (next b)).1 := by
    change a + 1 < b.1 + 1 + 1
    linarith
  have h1 := M_negative_expansion_positive _ _ ha1 hab1 N
  have h2 := M_negative_expansion_positive _ _ ha1 hab2 (N + 1)
  have hb2 : (next (next b)).1 = b.1 + 2 := by dsimp [next]; ring
  rw [hb2] at h2
  have hX : IsBigO atTop (fun X : ℝ => X) (fun X => X ^ (1 : ℝ)) := by
    aesop
  have h2X := hX.mul_atTop_rpow_of_isBigO_rpow 1
    _ (-a - ((N + 1 : ℕ))) h2 (by linarith)
  have h1' : IsBigO atTop
      (fun X => M (a + 1) (next b) (-X) - mExpansion (a + 1) (b.1 + 1) N X)
      (fun X => X ^ (-a - ((N + 1 : ℕ)))) := by
    convert h1 using 1
    · rfl
    grind
  have h := h1'.add (h2X.const_mul_left (-((a - b.1) / (b.1 * (b.1 + 1)))))
  apply h.congr'
  · filter_upwards [eventually_gt_atTop (0)] with X hXp
    rw [M_contiguous a, mExpansion_contiguous a b hab N X hXp]
    simp only [Pi.mul_apply]
    ring
  simp

/-- The complete algebraic expansion with its exact remainder order. -/
theorem M_negative_expansion 
    (ha : -1 < a) (hab : a < b.1) (N : ℕ) :
    IsBigO atTop (fun X => M a b (-X) - mExpansion a b.1 N X)
      (fun X => Real.rpow X (-a - (N : ℝ))) := by
  cases N with
  | succ N => exact M_negative_expansion_succ a b ha hab N
  | zero =>
    have h1 := (M_negative_expansion_succ a b ha hab 0).trans
      (rpow_isBigO_of_le (-a - ((0 + 1 : ℕ) : ℝ)) (-a) (by norm_num))
    have h0 : IsBigO atTop (mExpansion a b.1 1) (fun X : ℝ => X ^ (-a)) := by
      have h := (isBigO_refl (fun X : ℝ => X ^ (-a)) atTop)
        |>.const_mul_left (Real.Gamma b.1 / Real.Gamma (b.1 - a))
      convert h using 1
      ext X
      simp [mExpansion]
    have h := h1.add h0
    convert h using 1
    · ext X
      simp only [mExpansion]
      ring
    simp

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
