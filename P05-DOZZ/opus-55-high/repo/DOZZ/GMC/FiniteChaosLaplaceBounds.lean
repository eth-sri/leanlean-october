/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosInterpolationCalculus
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! Uniform bounds for the Gaussian-coordinate derivatives of finite-chaos Laplace tests. -/

@[expose] public section

namespace DOZZ.Proofs
section
variable {x : ℝ}

/-- The first scaled exponential moment is bounded on the nonnegative half-line. -/
lemma mul_exp_neg_le_one : x * Real.exp (-x) ≤ 1 := by
  have hxe : x ≤ Real.exp x := by
    linarith [Real.add_one_le_exp x]
  have hmul := mul_le_mul_of_nonneg_right hxe (le_of_lt (Real.exp_pos (-x)))
  rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hmul

/-- The second scaled exponential moment is bounded uniformly as well. -/
lemma sq_mul_exp_neg_le_four (hx : 0 ≤ x) : x ^ 2 * Real.exp (-x) ≤ 4 := by
  let y := x / 2
  have hy : 0 ≤ y := by positivity
  have hye : y ≤ Real.exp y := by
    linarith [Real.add_one_le_exp y]
  have hsq : y ^ 2 ≤ Real.exp y * Real.exp y := by
    nlinarith
  have hexp : Real.exp y * Real.exp y = Real.exp x := by
    rw [← Real.exp_add]
    aesop
  have hbound : x ^ 2 ≤ 4 * Real.exp x := by
    grind
  have hmul := mul_le_mul_of_nonneg_right hbound (le_of_lt (Real.exp_pos (-x)))
  rwa [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at hmul

end
section
variable {ι : Type*} [Fintype ι]
section
variable (a v : ι → ℝ)
section
variable (γ : ℝ)
section
variable (ha : ∀ i, 0 ≤ a i) (x : ι → ℝ)
include ha

/-- Each nonnegative Wick weight is bounded by the total finite-chaos mass. -/
lemma finiteChaosVectorWeight_le_mass
    (i : ι) :
    0 ≤ finiteChaosVectorWeight a v γ x i ∧
      finiteChaosVectorWeight a v γ x i ≤ finiteChaosVectorMass a v γ x := by
  classical
  have hweight : ∀ j, 0 ≤ finiteChaosVectorWeight a v γ x j := by
    intro j
    exact mul_nonneg (ha j) (Real.exp_nonneg _)
  constructor
  · simp_all
  · unfold finiteChaosVectorMass
    rw [← Finset.add_sum_erase Finset.univ (fun j => finiteChaosVectorWeight a v γ x j)
      (Finset.mem_univ i)]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun j hj => hweight j)

/-- The finite-chaos mass is nonnegative when all coefficients are nonnegative. -/
lemma finiteChaosVectorMass_nonneg
    :
    0 ≤ finiteChaosVectorMass a v γ x := by
  exact Finset.sum_nonneg fun i hi => mul_nonneg (ha i) (Real.exp_nonneg _)

end

end
section
variable (γ s : ℝ)
section
variable (ha : ∀ i, 0 ≤ a i) (hs : 0 ≤ s) (x : ι → ℝ)
include ha hs

/-- A Wick weight times the derivative of a Laplace test is uniformly bounded, independently of
the field coordinate. -/
lemma finiteChaos_laplace_first_weight_bound
    (i : ι) :
    ‖finiteChaosVectorWeight a v γ x i *
      (-s * Real.exp (-s * finiteChaosVectorMass a v γ x))‖ ≤ 1 := by
  have hmass := finiteChaosVectorWeight_le_mass a v γ ha x i
  have hm := finiteChaosVectorMass_nonneg a v γ ha x
  have hbound := mul_exp_neg_le_one (x := s * finiteChaosVectorMass a v γ x)
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass.2 hs)
    (le_of_lt (Real.exp_pos (-s * finiteChaosVectorMass a v γ x)))
  have hmul' :
      s * finiteChaosVectorWeight a v γ x i *
        Real.exp (-s * finiteChaosVectorMass a v γ x) ≤ 1 := by
    calc
      _ ≤ (s * finiteChaosVectorMass a v γ x) *
          Real.exp _ := hmul
      _ ≤ 1 := by
        simp_all
  simpa [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hmass.1,
    abs_of_nonneg hs, abs_of_nonneg (Real.exp_nonneg _), mul_assoc, mul_left_comm,
    mul_comm] using hmul'

/-- The product of two Wick weights times the second derivative of a Laplace test is bounded by
four, uniformly over all field coordinates. -/
lemma finiteChaos_laplace_second_weight_bound
    (i j : ι) :
    ‖finiteChaosVectorWeight a v γ x i * finiteChaosVectorWeight a v γ x j *
      (s ^ 2 * Real.exp (-s * finiteChaosVectorMass a v γ x))‖ ≤ 4 := by
  have hmass := finiteChaosVectorWeight_le_mass a v γ ha x i
  have hmassj := finiteChaosVectorWeight_le_mass a v γ ha x j
  have hm := finiteChaosVectorMass_nonneg a v γ ha x
  have hi :=
    mul_le_mul_of_nonneg_left hmass.2 hs
  have hj :=
    mul_le_mul_of_nonneg_left hmassj.2 hs
  have hprod :
      (s * finiteChaosVectorWeight a v γ x i) *
        (s * finiteChaosVectorWeight a v γ x j) ≤
      (s * finiteChaosVectorMass a v γ x) *
        (s * finiteChaosVectorMass a v γ x) :=
    mul_le_mul hi hj (mul_nonneg hs hmassj.1) (mul_nonneg hs hm)
  have hpow := sq_mul_exp_neg_le_four (mul_nonneg hs hm)
  have hpow' :
      (s * finiteChaosVectorMass a v γ x) ^ 2 *
        Real.exp (-s * finiteChaosVectorMass a v γ x) ≤ 4 := by
    simp_all
  have hbound :
      (s * finiteChaosVectorWeight a v γ x i) *
        (s * finiteChaosVectorWeight a v γ x j) *
          Real.exp (-s * finiteChaosVectorMass a v γ x) ≤ 4 := by
    calc
      _ ≤ (s * finiteChaosVectorMass a v γ x) ^ 2 *
          Real.exp (-s * finiteChaosVectorMass a v γ x) := by
            bound
      _ ≤ 4 := by
        assumption
  have hval : 0 ≤ finiteChaosVectorWeight a v γ x i *
      finiteChaosVectorWeight a v γ x j *
        (s ^ 2 * Real.exp (-s * finiteChaosVectorMass a v γ x)) :=
    by bound
  have hnorm :
      ‖finiteChaosVectorWeight a v γ x i * finiteChaosVectorWeight a v γ x j *
        (s ^ 2 * Real.exp (-s * finiteChaosVectorMass a v γ x))‖ =
      (s * finiteChaosVectorWeight a v γ x i) *
        (s * finiteChaosVectorWeight a v γ x j) *
          Real.exp (-s * finiteChaosVectorMass a v γ x) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hval]
    ring
  rwa [hnorm]

end

end

end


/-- The coordinate derivative of a Laplace score is uniformly bounded. This is the concrete
growth estimate needed to discharge the Gaussian Stein domination hypotheses for Laplace tests. -/
theorem finiteChaos_laplace_score_derivative_norm_le
    [DecidableEq ι]
    (a v : ι → ℝ) (γ s : ℝ) (ha : ∀ i, 0 ≤ a i) (hs : 0 ≤ s)
    (x : ι → ℝ) (i j : ι) :
    ‖γ * (if i = j then finiteChaosVectorWeight a v γ x i *
        (-s * Real.exp (-s * finiteChaosVectorMass a v γ x)) else 0) +
      γ * finiteChaosVectorWeight a v γ x i *
        finiteChaosVectorWeight a v γ x j *
          (s ^ 2 * Real.exp (-s * finiteChaosVectorMass a v γ x))‖ ≤
      5 * |γ| := by
  have hfirst := finiteChaos_laplace_first_weight_bound a v γ s ha hs x i
  have hdiag :
      ‖(if i = j then finiteChaosVectorWeight a v γ x i *
          (-s * Real.exp (-s * finiteChaosVectorMass a v γ x)) else 0)‖ ≤ 1 := by
    aesop
  have hadd := norm_add_le
    (γ * (if i = j then finiteChaosVectorWeight a v γ x i *
        (-s * Real.exp (-s * finiteChaosVectorMass a v γ x)) else 0))
    (γ * finiteChaosVectorWeight a v γ x i *
      finiteChaosVectorWeight a v γ x j *
        (s ^ 2 * Real.exp (-s * finiteChaosVectorMass a v γ x)))
  have hmul1 :
      ‖γ * (if i = j then finiteChaosVectorWeight a v γ x i *
          (-s * Real.exp (-s * finiteChaosVectorMass a v γ x)) else 0)‖ ≤ |γ| := by
    calc
      _ = |γ| * ‖if i = j then finiteChaosVectorWeight a v γ x i *
          (-s * Real.exp _) else 0‖ := by
            bound
      _ ≤ |γ| * 1 := mul_le_mul_of_nonneg_left hdiag (abs_nonneg γ)
      _ = |γ| := by ring
  have hmul2 :
      ‖γ * finiteChaosVectorWeight a v γ x i *
          finiteChaosVectorWeight a v γ x j *
            (s ^ 2 * Real.exp (-s * finiteChaosVectorMass a v γ x))‖ ≤ 4 * |γ| := by
    calc
      _ = |γ| * ‖finiteChaosVectorWeight a v γ x i *
          finiteChaosVectorWeight a v γ x j *
            (s ^ 2 * Real.exp _)‖ := by
              rw [show γ * finiteChaosVectorWeight a v γ x i *
                  finiteChaosVectorWeight a v γ x j *
                    (s ^ 2 * Real.exp _) =
                  γ * (finiteChaosVectorWeight a v γ x i *
                    finiteChaosVectorWeight a v γ x j *
                      (s ^ 2 * Real.exp _)) by ring,
                norm_mul, Real.norm_eq_abs]
      _ ≤ |γ| * 4 := mul_le_mul_of_nonneg_left (finiteChaos_laplace_second_weight_bound a v γ s ha hs x i j) (abs_nonneg γ)
      _ = 4 * |γ| := by ring
  calc
    _ ≤ |γ| + 4 * |γ| := by
      calc
        _ ≤ ‖γ * (if i = j then finiteChaosVectorWeight a v γ x i *
              (-s * Real.exp _) else 0)‖ +
            ‖γ * finiteChaosVectorWeight a v γ x i *
              finiteChaosVectorWeight a v γ x j *
                (s ^ 2 * Real.exp _)‖ := hadd
        _ ≤ |γ| + 4 * |γ| := add_le_add hmul1 hmul2
    _ = 5 * |γ| := by ring

end

end DOZZ.Proofs
