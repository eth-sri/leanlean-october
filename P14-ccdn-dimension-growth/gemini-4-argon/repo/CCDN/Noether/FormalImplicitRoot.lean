/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.PowerSeries.Basic
import CCDN.ForMathlib.Polynomial
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.SimpleRing.Principal

/-! A simple root over the constant field lifts to a formal power
series root. Newton iteration and coefficient stabilization prove existence. -/

@[expose] public section
namespace CCDN
noncomputable section

private def formalNewtonSequence {K : Type*} [Field K]
    (f : Polynomial (PowerSeries K)) (b u : K) : ℕ → PowerSeries K
  | 0 => PowerSeries.C b
  | n + 1 => formalNewtonSequence f b u n - PowerSeries.C u * f.eval (formalNewtonSequence f b u n)

/-- Every simple root of the constant polynomial lifts to a formal root. -/
theorem exists_formal_simple_root {K : Type*} [Field K]
    (f : Polynomial (PowerSeries K)) (b : K)
    (hroot : (f.map PowerSeries.constantCoeff).eval b = 0)
    (hder : (f.derivative.map PowerSeries.constantCoeff).eval b ≠ 0) :
    ∃ g : PowerSeries K, PowerSeries.constantCoeff g = b ∧ f.eval g = 0 := by
  let u := ((f.derivative.map PowerSeries.constantCoeff).eval b)⁻¹
  have hu : u * (f.derivative.map PowerSeries.constantCoeff).eval b = 1 := inv_mul_cancel₀ hder
  have hprec (n : ℕ) : PowerSeries.constantCoeff (formalNewtonSequence f b u n) = b ∧
      PowerSeries.X ^ (n + 1) ∣ f.eval (formalNewtonSequence f b u n) := by
    induction n with
    | zero =>
      refine ⟨by simp [formalNewtonSequence], ?_⟩
      rw [zero_add, pow_one, PowerSeries.X_dvd_iff]
      simp only [formalNewtonSequence, ← Polynomial.eval_map_apply, PowerSeries.constantCoeff_C, hroot]
    | succ n ih =>
      let gn := formalNewtonSequence f b u n
      let gn' := gn - PowerSeries.C u * f.eval gn
      refine ⟨by simp only [formalNewtonSequence, map_sub, map_mul, PowerSeries.constantCoeff_C,
        ← Polynomial.eval_map_apply, ih.1, hroot, mul_zero, sub_zero], ?_⟩
      have hXf : (PowerSeries.X : PowerSeries K) ∣ f.eval gn := by
        simpa only [pow_one] using (pow_dvd_pow PowerSeries.X (by omega : 1 ≤ n + 1)).trans ih.2
      have hXdiff : (PowerSeries.X : PowerSeries K) ∣ gn' - gn := by
        convert dvd_neg.mpr (dvd_mul_of_dvd_right hXf (PowerSeries.C u)) using 1
        dsimp [gn']; ring
      obtain ⟨q, he, hq⟩ := Polynomial.exists_divided_difference f gn' gn
      have hbase : (PowerSeries.X : PowerSeries K) ∣ 1 - PowerSeries.C u * f.derivative.eval gn :=
        PowerSeries.X_dvd_iff.mpr (by simp only [gn, map_sub, map_one, map_mul,
          PowerSeries.constantCoeff_C, ← Polynomial.eval_map_apply, ih.1, hu, sub_self])
      have hbracket : (PowerSeries.X : PowerSeries K) ∣ 1 - PowerSeries.C u * q := by
        convert dvd_sub hbase (dvd_mul_of_dvd_left (hXdiff.trans hq) (PowerSeries.C u)) using 1; ring
      have heq : f.eval gn' = f.eval gn * (1 - PowerSeries.C u * q) := by
        dsimp only [gn'] at he; linear_combination he
      change PowerSeries.X ^ (n + 1 + 1) ∣ f.eval gn'
      rw [heq, pow_succ]
      exact mul_dvd_mul ih.2 hbracket
  let g := PowerSeries.mk (fun n => PowerSeries.coeff n (formalNewtonSequence f b u n))
  have hstab {n m : ℕ} (hnm : n ≤ m) :
      PowerSeries.X ^ (n + 1) ∣ formalNewtonSequence f b u m - formalNewtonSequence f b u n := by
    induction m, hnm using Nat.le_induction with
    | base => simp
    | succ m hnm ih =>
      have hd := (pow_dvd_pow (PowerSeries.X : PowerSeries K) (Nat.add_le_add_right hnm 1)).trans
        (hprec m).2
      convert dvd_sub ih (dvd_mul_of_dvd_right hd (PowerSeries.C u)) using 1
      simp only [formalNewtonSequence]; ring
  have happrox (n : ℕ) : PowerSeries.X ^ (n + 1) ∣ g - formalNewtonSequence f b u n := by
    refine PowerSeries.X_pow_dvd_iff.mpr fun j hj => ?_
    have hc := PowerSeries.X_pow_dvd_iff.mp (hstab (show j ≤ n by omega)) j (by omega)
    simp only [map_sub] at hc ⊢
    dsimp only [g]
    rw [PowerSeries.coeff_mk]
    exact sub_eq_zero.mpr (sub_eq_zero.mp hc).symm
  refine ⟨g, ?_, PowerSeries.ext fun n => ?_⟩
  · have hc := PowerSeries.X_dvd_iff.mp (by simpa only [zero_add, pow_one] using happrox 0)
    simpa only [map_sub, formalNewtonSequence, PowerSeries.constantCoeff_C, sub_eq_zero] using hc
  · have hdiff := (happrox n).trans (Polynomial.sub_dvd_eval_sub g (formalNewtonSequence f b u n) f)
    have hh : PowerSeries.X ^ (n + 1) ∣ f.eval g := by
      convert dvd_add hdiff (hprec n).2 using 1; ring
    simpa only [map_zero] using PowerSeries.X_pow_dvd_iff.mp hh n (by omega)

/-- The simple formal branch is unique among roots with the chosen constant. -/
theorem formal_simple_root_unique {K : Type*} [Field K]
    (f : Polynomial (PowerSeries K)) (b : K)
    (hder : (f.derivative.map PowerSeries.constantCoeff).eval b ≠ 0)
    {g h : PowerSeries K} (hg : PowerSeries.constantCoeff g = b)
    (hh : PowerSeries.constantCoeff h = b) (hfg : f.eval g = 0) (hfh : f.eval h = 0) : g = h := by
  obtain ⟨q, he, hq⟩ := Polynomial.exists_divided_difference f g h
  have hc := PowerSeries.X_dvd_iff.mp
    ((PowerSeries.X_dvd_iff.mpr (by simp [hg, hh])).trans hq)
  simp only [map_sub, ← Polynomial.eval_map_apply, hh, sub_eq_zero] at hc
  have hq0 : q ≠ 0 := fun hz => hder (by simpa only [hz, map_zero] using hc.symm)
  rw [hfg, hfh, sub_self] at he
  exact sub_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right hq0)

end
end CCDN
