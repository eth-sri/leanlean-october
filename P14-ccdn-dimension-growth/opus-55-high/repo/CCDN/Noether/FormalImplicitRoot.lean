/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.PowerSeries.Basic
import CCDN.ForMathlib.Polynomial
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.SimpleRing.Principal

/-! A simple root over the constant field lifts to a formal power
series root. Newton iteration and coefficient stabilization prove existence. -/

namespace CCDN
noncomputable section

def formalNewtonSequence {K : Type*} [Field K]
    (f : Polynomial (PowerSeries K)) (b u : K) : ℕ → PowerSeries K
  | 0 => PowerSeries.C b
  | n + 1 => formalNewtonSequence f b u n - PowerSeries.C u * f.eval (formalNewtonSequence f b u n)

variable {K : Type*} [Field K] (f : Polynomial (PowerSeries K))

lemma formalNewton_step
    (b u : K)
    (hu : u * (f.derivative.map PowerSeries.constantCoeff).eval b = 1)
    (g : PowerSeries K) (hg : PowerSeries.constantCoeff g = b)
    {k : ℕ} (hk : 1 ≤ k) (hfg : PowerSeries.X ^ k ∣ f.eval g) :
    PowerSeries.X ^ (k + 1) ∣ f.eval (g - PowerSeries.C u * f.eval g) := by
  let g' := g - PowerSeries.C u * f.eval g
  have hXdiff : PowerSeries.X ∣ g' - g := by
    have hh := dvd_mul_of_dvd_right (by
      simpa using (pow_dvd_pow PowerSeries.X hk).trans hfg) (PowerSeries.C u)
    aesop
  obtain ⟨q, he, hq⟩ := Polynomial.exists_divided_difference f g' g
  have hqder := hXdiff.trans hq
  have hbase : PowerSeries.X ∣ 1 - PowerSeries.C u * f.derivative.eval g := by
    apply PowerSeries.X_dvd_iff.mpr
    aesop
  have heq : f.eval g' = f.eval g * (1 - PowerSeries.C u * q) := by grind
  rw [heq, pow_succ]
  exact mul_dvd_mul hfg (by
    have hh := dvd_mul_of_dvd_left hqder (PowerSeries.C u)
    convert dvd_sub hbase hh using 1
    ring)

lemma formalNewton_precision
    (b u : K)
    (hroot : (f.map PowerSeries.constantCoeff).eval b = 0)
    (hu : u * (f.derivative.map PowerSeries.constantCoeff).eval b = 1) (n : ℕ) :
    PowerSeries.constantCoeff (formalNewtonSequence f b u n) = b ∧
      PowerSeries.X ^ (n + 1) ∣ f.eval (formalNewtonSequence f b u n) := by
  induction n with
  | zero =>
      refine ⟨by aesop, ?_⟩
      rw [show (0 : ℕ) + 1 = 1 by omega, pow_one]
      apply PowerSeries.X_dvd_iff.mpr
      simp [formalNewtonSequence, ← Polynomial.eval_map_apply, PowerSeries.constantCoeff_C,
        hroot]
  | succ n ih =>
      refine ⟨?_, formalNewton_step f b u hu _ ih.1 (by omega) ih.2⟩
      simp [formalNewtonSequence, map_sub, map_mul, PowerSeries.constantCoeff_C,
        ← Polynomial.eval_map_apply, ih.1, hroot, mul_zero, sub_zero]

lemma formalNewton_stabilizes
    (b u : K)
    (hroot : (f.map PowerSeries.constantCoeff).eval b = 0)
    (hu : u * (f.derivative.map PowerSeries.constantCoeff).eval b = 1)
    {n m : ℕ} (hnm : n ≤ m) :
    PowerSeries.X ^ (n + 1) ∣ formalNewtonSequence f b u m - formalNewtonSequence f b u n := by
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
      have hprec := (formalNewton_precision f b u hroot hu m).2
      have hd := (pow_dvd_pow PowerSeries.X (Nat.add_le_add_right hnm 1)).trans
        hprec
      have hh := dvd_mul_of_dvd_right hd (PowerSeries.C u)
      convert dvd_sub ih hh using 1
      simp [formalNewtonSequence]
      ring

/-- Every simple root of the constant polynomial lifts to a formal root. -/
theorem exists_formal_simple_root
    (b : K)
    (hroot : (f.map PowerSeries.constantCoeff).eval b = 0)
    (hder : (f.derivative.map PowerSeries.constantCoeff).eval b ≠ 0) :
    ∃ g : PowerSeries K, PowerSeries.constantCoeff g = b ∧ f.eval g = 0 := by
  let u := ((f.derivative.map PowerSeries.constantCoeff).eval b)⁻¹
  have hu := inv_mul_cancel₀ hder
  let g := PowerSeries.mk (fun n => PowerSeries.coeff n (formalNewtonSequence f b u n))
  have happrox (n : ℕ) : PowerSeries.X ^ (n + 1) ∣ g - formalNewtonSequence f b u n := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro j hj
    have hh := formalNewton_stabilizes f b u hroot hu (show j ≤ n by omega)
    have hc := PowerSeries.X_pow_dvd_iff.mp hh j (by omega)
    grind [PowerSeries.coeff_mk]
  refine ⟨g, ?_, ?_⟩
  · aesop
  · apply PowerSeries.ext
    intro n
    have hdiff := (happrox n).trans (Polynomial.sub_dvd_eval_sub g (formalNewtonSequence f b u n) f)
    have hprec := (formalNewton_precision f b u hroot hu n).2
    have hh : PowerSeries.X ^ (n + 1) ∣ f.eval g := by
      convert dvd_add hdiff hprec using 1
      ring
    have hc := PowerSeries.X_pow_dvd_iff.mp hh n (by omega)
    grind

