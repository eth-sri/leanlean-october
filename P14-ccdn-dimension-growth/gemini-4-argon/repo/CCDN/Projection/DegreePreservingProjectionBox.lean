/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Height.Box
public import CCDN.Projection.CurvePrimitivePair
public import Mathlib.Data.Fin.VecNotation

/-!
Integral evaluation and coefficient-uniform height control for the two
moment coordinates in the degree-preserving projection.

Evaluation of the moment coordinates used by the bounded primitive pair.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Evaluating the moment coordinate with parameter `k` at `z` gives `∑ j, k ^ j * z j`. -/
lemma momentCoordinate_eval {K : Type*} [CommRing K] {n : ℕ}
    (k : ℕ) (z : Fin n → K) :
    eval z (momentCoordinate K n k) = ∑ j : Fin n, (k : K) ^ j.val * z j := by
  simp only [momentCoordinate, map_sum, map_mul, eval_C, eval_X]

/-- The integer projection of `ℤⁿ` to `ℤ²` given by the two moment coordinates with parameters `k₀`
and `k₁`. -/
def degreeProjection (n k₀ k₁ : ℕ) (z : IntPoint n) : IntPoint 2 :=
  ![eval z (momentCoordinate ℤ n k₀), eval z (momentCoordinate ℤ n k₁)]

/-- The box scaling factor `(n + 1) * ((n + 1) * (d + 1)) ^ (2 * n)` for the moment projection in
`n` variables and degree `d`. -/
def projectionBoxFactor (n d : ℕ) : ℝ :=
  ((n : ℝ) + 1) * ((((n : ℝ) + 1) * ((d : ℝ) + 1)) ^ 2) ^ n

/-- The box scaling factor of the moment projection is at least one. -/
lemma projectionBoxFactor_one_le (n d : ℕ) : 1 ≤ projectionBoxFactor n d := by
  unfold projectionBoxFactor
  have hn : (1 : ℝ) ≤ n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hd : (1 : ℝ) ≤ d + 1 := by linarith [Nat.cast_nonneg (α := ℝ) d]
  have hp : (1 : ℝ) ≤ ((((n : ℝ) + 1) * ((d : ℝ) + 1)) ^ 2) ^ n :=
    one_le_pow₀ (one_le_pow₀ (by nlinarith))
  nlinarith

/-- For parameters `k₀ ≤ n ^ 2 * d` and `k₁ ≤ n * d ^ 2`, the moment projection maps the integer box
of radius `B` into the integer box of radius `projectionBoxFactor n d * B`. -/
theorem degreeProjection_box {n d k₀ k₁ : ℕ} (hk₀ : k₀ ≤ n ^ 2 * d)
    (hk₁ : k₁ ≤ n * d ^ 2) {B : ℝ} (hB : 0 ≤ B)
    {z : IntPoint n} (hz : z ∈ integerBox n B) :
    degreeProjection n k₀ k₁ z ∈ integerBox 2 (projectionBoxFactor n d * B) := by
  let M : ℝ := (((n : ℝ) + 1) * ((d : ℝ) + 1)) ^ 2
  have hn : (0 : ℝ) ≤ n := by positivity
  have hd : (0 : ℝ) ≤ d := by positivity
  have hM : 1 ≤ M := one_le_pow₀ (by nlinarith [mul_nonneg hn hd])
  have hb := mem_integerBox.mp hz
  have hht {k : ℕ} (hk : (k : ℝ) ≤ M) :
      |(eval z (momentCoordinate ℤ n k) : ℝ)| ≤ projectionBoxFactor n d * B := by
    rw [momentCoordinate_eval, Int.cast_sum]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    refine ((Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun j _ => (?_ : _ ≤ M ^ n * B)).trans_eq
        (show ∑ _j : Fin n, M ^ n * B = n * M ^ n * B by simp; ring))).trans
      (by unfold projectionBoxFactor; gcongr; norm_num)
    simp only [abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    exact mul_le_mul ((pow_le_pow_left₀ (by positivity) hk j.val).trans
      (pow_le_pow_right₀ hM (Nat.le_of_lt j.isLt))) (hb j) (abs_nonneg _) (by positivity)
  refine mem_integerBox.mpr fun j => ?_
  fin_cases j
  · exact hht ((show (k₀ : ℝ) ≤ (n : ℝ) ^ 2 * d from mod_cast hk₀).trans
      ((mul_le_mul (pow_le_pow_left₀ hn (by linarith : (n : ℝ) ≤ (n : ℝ) + 1) 2)
        (show (d : ℝ) ≤ ((d : ℝ) + 1) ^ 2 by nlinarith [sq_nonneg (d : ℝ)]) hd
        (by positivity)).trans_eq (by dsimp [M]; ring)))
  · exact hht ((show (k₁ : ℝ) ≤ (n : ℝ) * d ^ 2 from mod_cast hk₁).trans
      ((mul_le_mul (show (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 by nlinarith [sq_nonneg (n : ℝ)])
        (pow_le_pow_left₀ hd (by linarith : (d : ℝ) ≤ (d : ℝ) + 1) 2) (by positivity)
        (by positivity)).trans_eq (by dsimp [M]; ring)))

/-- Evaluating the integer moment coordinate at an integer point and casting to `ℚ` agrees with
evaluating the rational moment coordinate at the corresponding rational point. -/
lemma rationalPoint_moment_eval {n : ℕ} (k : ℕ) (z : IntPoint n) :
    (eval z (momentCoordinate ℤ n k) : ℚ) =
      eval (rationalPoint z) (momentCoordinate ℚ n k) := by
  simp [momentCoordinate_eval, rationalPoint]

/-- The rational point of the integer moment projection of `z` is the pair of rational moment
coordinates evaluated at `z`. -/
lemma rationalPoint_degreeProjection {n k₀ k₁ : ℕ} (z : IntPoint n) :
    rationalPoint (degreeProjection n k₀ k₁ z) =
      ![eval (rationalPoint z) (momentCoordinate ℚ n k₀),
        eval (rationalPoint z) (momentCoordinate ℚ n k₁)] := by
  funext j
  fin_cases j <;> exact rationalPoint_moment_eval _ _

end
end CCDN
