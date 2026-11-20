module

public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.RingTheory.PowerSeries.WellKnown

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Formal logarithm and exponential composition

This module develops the formal composition identities between Mathlib's
`PowerSeries.log` and `PowerSeries.exp` that are used by the local-field
logarithm and exponential.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace PowerSeries

section

variable (A : Type*) [CommRing A] [IsAddTorsionFree A] {f : PowerSeries A}

/-- A torsion-free power series with zero constant coefficient satisfying
`f' * (1 + X) = f` is zero. -/
theorem eq_zero_of_derivative_mul_one_add_X_eq_self
    (hD :
      PowerSeries.derivative f * (1 + PowerSeries.X : PowerSeries A) = f)
    (hc : PowerSeries.constantCoeff f = 0) :
    f = 0 := by
  ext n
  induction n with
  | zero =>
      rw [PowerSeries.coeff_zero_eq_constantCoeff, hc]
      simp
  | succ n ih =>
      cases n with
      | zero =>
          have hcoeff := congrArg (PowerSeries.coeff 0) hD
          have hmul :
              PowerSeries.derivative f *
                  (1 + PowerSeries.X : PowerSeries A) =
                PowerSeries.derivative f +
                  PowerSeries.derivative f * PowerSeries.X := by
            ring
          rw [hmul, map_add, PowerSeries.coeff_zero_mul_X,
            add_zero, PowerSeries.coeff_zero_eq_constantCoeff, hc] at hcoeff
          rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
            PowerSeries.coeff_derivative] at hcoeff
          simpa using hcoeff
      | succ n =>
          have hcoeff := congrArg (PowerSeries.coeff (n + 1)) hD
          have hmul :
              PowerSeries.derivative f *
                  (1 + PowerSeries.X : PowerSeries A) =
                PowerSeries.derivative f +
                  PowerSeries.derivative f * PowerSeries.X := by
            ring
          rw [hmul, map_add, PowerSeries.coeff_succ_mul_X,
            PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at hcoeff
          simp [ih] at hcoeff
          have hzero :
              PowerSeries.coeff (n + 2) f *
                  ((Nat.succ (n + 1) : ℕ) : A) = 0 := by
            simpa using hcoeff
          rw [mul_comm, ← nsmul_eq_mul] at hzero
          simpa using
            (smul_right_inj (Nat.succ_ne_zero (n + 1))).mp
              (by simpa using hzero)

/-- A torsion-free power series with constant coefficient one satisfying
`f' * (1 + X) = f` is `1 + X`. -/
theorem eq_one_add_X_of_derivative_mul_one_add_X_eq_self
    (hD :
      PowerSeries.derivative f * (1 + PowerSeries.X : PowerSeries A) = f)
    (hc : PowerSeries.constantCoeff f = 1) :
    f = 1 + PowerSeries.X := by
  have hbase :
      PowerSeries.derivative (1 + PowerSeries.X : PowerSeries A) *
          (1 + PowerSeries.X : PowerSeries A) =
        (1 + PowerSeries.X : PowerSeries A) := by
    simp
  have hzero :
      PowerSeries.derivative (f - (1 + PowerSeries.X : PowerSeries A)) *
          (1 + PowerSeries.X : PowerSeries A) =
        f - (1 + PowerSeries.X : PowerSeries A) := by
    rw [map_sub, sub_mul, hD, hbase]
  have hczero :
      PowerSeries.constantCoeff
          (f - (1 + PowerSeries.X : PowerSeries A)) = 0 := by
    simp [hc]
  have h := eq_zero_of_derivative_mul_one_add_X_eq_self
    A hzero hczero
  exact sub_eq_zero.mp h

/-- A power series with derivative one and constant coefficient zero is `X`. -/
theorem eq_X_of_derivative_eq_one
    (hD : PowerSeries.derivative f = 1)
    (hc : PowerSeries.constantCoeff f = 0) :
    f = PowerSeries.X := by
  apply PowerSeries.derivative.ext
  · simp [hD]
  · simp [hc]

end

variable (A : Type*) [CommRing A] [Algebra ℚ A] [IsAddTorsionFree A]

/-- Substituting Mathlib's formal logarithm into its exponential yields
`1 + X`. -/
theorem exp_subst_log_eq_one_add_X :
    PowerSeries.subst (PowerSeries.log A) (PowerSeries.exp A) =
      (1 + PowerSeries.X : PowerSeries A) := by
  apply subst_exp_log

/-- Substituting `exp - 1` into Mathlib's formal logarithm yields `X`. -/
theorem log_subst_exp_sub_one_eq_X :
    PowerSeries.subst ((PowerSeries.exp A) - 1) (PowerSeries.log A) =
      (PowerSeries.X : PowerSeries A) := by
  apply subst_log_exp_sub_one

end PowerSeries

end
