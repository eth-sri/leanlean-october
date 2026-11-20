/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Topology.MetricSpace.Basic
public import DOZZ.DOZZAlgebra.GenericLocus
public import DOZZ.DOZZAlgebra.ReflectionShiftForm

/-!
# DOZZ — reflection coefficient shift identities
-/

@[expose] public section

open Complex Filter Metric Set Topology

namespace DOZZ.Proofs

private lemma eventually_affine_Gamma_ne_zero {c d : ℂ} (hc : c ≠ 0) :
    ∀ᶠ α : ℂ in codiscrete ℂ, Complex.Gamma (c * α + d) ≠ 0 := by
  filter_upwards [eventually_affine_ne_neg_nat hc] with α hα
  apply Complex.Gamma_ne_zero <;> assumption

private lemma lFun_one_sub {z : ℂ} (hz : z ≠ 0) :
    lFun (1 - z) = -z * (Complex.Gamma (-z) / Complex.Gamma z) := by
  have hnum : Complex.Gamma (1 - z) = -z * Complex.Gamma (-z) := by
    calc
      Complex.Gamma (1 - z) = Complex.Gamma (-z + 1) := by congr 1; ring
      _ = -z * Complex.Gamma (-z) :=
        Complex.Gamma_add_one (-z) (neg_ne_zero.mpr hz)
  have hden : 1 - (1 - z) = z := by ring
  unfold lFun
  rw [hnum, hden]
  simp only [div_eq_mul_inv]
  ring

private lemma lFun_one_add {z : ℂ} (hz : z ≠ 0) :
    lFun (1 + z) = z * (Complex.Gamma z / Complex.Gamma (-z)) := by
  have hnum : Complex.Gamma (1 + z) = z * Complex.Gamma z := by
    calc
      Complex.Gamma (1 + z) = Complex.Gamma (z + 1) := by congr 1; ring
      _ = z * Complex.Gamma z := Complex.Gamma_add_one z hz
  have hden : 1 - (1 + z) = -z := by ring
  unfold lFun
  rw [hnum, hden]
  simp only [div_eq_mul_inv]
  ring

private lemma eventually_Gamma_Qsub_affine {Q c d : ℂ} (hc : c ≠ 0) :
    ∀ᶠ α : ℂ in codiscrete ℂ, Complex.Gamma (c * (Q - α) + d) ≠ 0 := by
  have h := eventually_affine_Gamma_ne_zero (c := -c) (d := c * Q + d)
    (neg_ne_zero.mpr hc)
  grind

private lemma reflectionBase_pos {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ) :
    0 < dozzBase γ μ := by
  have hq : γ ^ 2 / 4 < 1 := by linarith [pow_lt_pow_left₀ hγ2 hγ.le two_ne_zero]
  rw [dozzBase, lFun_gammaSq_real, Complex.ofReal_re]
  positivity

private lemma lFun_real_factors {q : ℝ} (hq : 0 < q) (hn : ∀ n : ℕ, q ≠ n) :
    lFun (q : ℂ) * lFun (-(q : ℂ)) = -1 / (q : ℂ) ^ 2 := by
  apply lFun_mul_neg (by exact_mod_cast hq.ne')
  · rw [Complex.Gamma_ofReal]
    exact_mod_cast (Real.Gamma_pos_of_pos hq).ne'
  · apply Complex.Gamma_ne_zero
    intro n h
    apply hn n
    exact_mod_cast (neg_inj.mp h : (q : ℂ) = n)

private noncomputable def reflectionGammaRatio (z : ℂ) : ℂ := Complex.Gamma (-z) / Complex.Gamma z

private lemma reflectionGammaRatio_add_one {z : ℂ} (hz : z ≠ 0) (hz1 : z + 1 ≠ 0) :
    reflectionGammaRatio (z + 1) = -reflectionGammaRatio z / (z * (z + 1)) := by
  have h := Complex.Gamma_add_one (-(z + 1)) (neg_ne_zero.mpr hz1)
  rw [show -(z + 1) + 1 = -z by ring] at h
  have he : Complex.Gamma (-(z + 1)) = Complex.Gamma (-z) / (-(z + 1)) := by
    apply (eq_div_iff (neg_ne_zero.mpr hz1)).2
    simpa only [mul_comm] using h.symm
  rw [reflectionGammaRatio, reflectionGammaRatio, he, Complex.Gamma_add_one z hz]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_neg]
  ring

private lemma gamma_ne_zero_arg {z : ℂ} (h : Complex.Gamma z ≠ 0) : z ≠ 0 := by
  rintro rfl
  simp at h

/-- Shift one Gamma ratio by one and the other by their proportional increment. -/
private lemma reflectionGammaRatio_step {t p q : ℂ} (ht : t = q * p) (hp1 : p + 1 ≠ 0)
    (hT : Complex.Gamma t ≠ 0) (hP : Complex.Gamma p ≠ 0)
    (hU : Complex.Gamma (t + q) ≠ 0) (hNU : Complex.Gamma (-(t + q)) ≠ 0) :
    (reflectionGammaRatio (t + q) * reflectionGammaRatio (p + 1)) *
        (lFun (1 - t) * lFun (1 + (t + q))) = q ^ 2 * (reflectionGammaRatio t * reflectionGammaRatio p) := by
  have hp := gamma_ne_zero_arg hP
  rw [lFun_one_sub (gamma_ne_zero_arg hT), lFun_one_add (gamma_ne_zero_arg hU), reflectionGammaRatio_add_one hp hp1]
  simp only [reflectionGammaRatio]
  field_simp [hT, hP, hU, hNU, hp, hp1]
  rw [ht]
  ring

private noncomputable def reflectionShiftModel (B b c e A : ℂ) : ℂ :=
  -B ^ (e * A) * reflectionGammaRatio (b * A) * reflectionGammaRatio (c * A)

private lemma reflectionShiftModel_swap (B b c e A : ℂ) :
    reflectionShiftModel B b c e A = reflectionShiftModel B c b e A := by
  unfold reflectionShiftModel
  ring

/-- A single proportional shift rule covers both reflection steps. The translation `r` chooses
which side of the shift is indexed by the original charge. -/
private theorem reflectionShiftModel_step (B b c e r : ℂ) (hbc : b * c = 1) (hB : B ≠ 0)
    (hprod : lFun (b ^ 2) * lFun (-(b ^ 2)) = -1 / (b ^ 2) ^ 2) :
    ∀ᶠ α : ℂ in codiscrete ℂ,
      let A := b + c - (α + r)
      reflectionShiftModel B b c e (A + b) =
        -(B ^ (e * b) / lFun (b ^ 2)) * reflectionShiftModel B b c e A /
          (lFun (-(b ^ 2)) * lFun (b * α + b * r - b ^ 2) * lFun (2 + 2 * b ^ 2 - (b * α + b * r))) := by
  have hb : b ≠ 0 := left_ne_zero_of_mul (by rw [hbc]; exact one_ne_zero)
  have hc : c ≠ 0 := right_ne_zero_of_mul (by rw [hbc]; exact one_ne_zero)
  let q := b ^ 2
  let Qc := b + c - r
  have hq : q ≠ 0 := pow_ne_zero _ hb
  have hneg := neg_ne_zero.mpr hb
  filter_upwards [eventually_Gamma_Qsub_affine (Q := Qc) (d := 0) hb,
    eventually_Gamma_Qsub_affine (Q := Qc) (d := 0) hneg,
    eventually_Gamma_Qsub_affine (Q := Qc) (d := q) hb,
    eventually_Gamma_Qsub_affine (Q := Qc) (d := -q) hneg,
    eventually_Gamma_Qsub_affine (Q := Qc) (d := 0) hc] with α ht hnt hu hnu hp
  dsimp only
  let A := b + c - (α + r)
  let t := b * A
  let p := c * A
  have hA : Qc - α = A := by dsimp [Qc, A]; ring
  rw [hA] at ht hnt hu hnu hp
  have ht' : Complex.Gamma t ≠ 0 := by simpa [t] using ht
  have hnt' : Complex.Gamma (-t) ≠ 0 := by simpa [t] using hnt
  have hu' : Complex.Gamma (t + q) ≠ 0 := hu
  have hnu' : Complex.Gamma (-(t + q)) ≠ 0 := by simpa [t, neg_add, add_comm] using hnu
  have hp' : Complex.Gamma p ≠ 0 := by simpa [p] using hp
  have htp : t = q * p := by dsimp [t, q, p]; linear_combination -(b * A) * hbc
  have hp1 : p + 1 ≠ 0 := by
    intro h
    apply gamma_ne_zero_arg hu'
    rw [htp, ← mul_add_one, h, mul_zero]
  have hgamma := reflectionGammaRatio_step htp hp1 ht' hp' hu' hnu'
  have hprod' : lFun q * lFun (-q) = -1 / q ^ 2 := hprod
  have hqneg : lFun q * lFun (-q) ≠ 0 := by
    rw [hprod']
    exact div_ne_zero (by norm_num) (pow_ne_zero _ hq)
  have hL1 : lFun (1 - t) ≠ 0 := by
    rw [lFun_one_sub (gamma_ne_zero_arg ht')]
    exact mul_ne_zero (neg_ne_zero.mpr (gamma_ne_zero_arg ht')) (div_ne_zero hnt' ht')
  have hL2 : lFun (1 + (t + q)) ≠ 0 := by
    rw [lFun_one_add (gamma_ne_zero_arg hu')]
    exact mul_ne_zero (gamma_ne_zero_arg hu') (div_ne_zero hu' hnu')
  have hcoeff : q ^ 2 * lFun (-q) = -1 / lFun q := by
    apply (eq_div_iff (left_ne_zero_of_mul hqneg)).2
    rw [mul_assoc, mul_comm (lFun (-q)), hprod']
    field_simp [hq]
  change reflectionShiftModel B b c e (A + b) = _
  have harg1 : b * α + b * r - b ^ 2 = 1 - t := by
    dsimp [t, A]; linear_combination hbc
  have harg2 : 2 + 2 * b ^ 2 - (b * α + b * r) = 1 + (t + q) := by
    dsimp [t, A, q]; linear_combination -hbc
  rw [harg1, harg2]
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (right_ne_zero_of_mul hqneg) hL1) hL2)).2
  rw [reflectionShiftModel, reflectionShiftModel, show b * (A + b) = t + q by dsimp [t, q]; ring,
    show c * (A + b) = p + 1 by dsimp [p]; linear_combination hbc,
    show e * (A + b) = e * b + e * A by ring, Complex.cpow_add _ _ hB]
  calc
    _ = -(B ^ (e * b) * B ^ (e * A)) *
        ((reflectionGammaRatio (t + q) * reflectionGammaRatio (p + 1)) * (lFun (1 - t) * lFun (1 + (t + q)))) *
        lFun (-q) := by ring
    _ = _ := by rw [hgamma]; linear_combination -(B ^ (e * b) * B ^ (e * A) * reflectionGammaRatio t * reflectionGammaRatio p) * hcoeff

private lemma reflectionDOZZ_eq_shiftModel (γ μ : ℝ) (α : ℂ) :
    reflectionDOZZ γ μ α =
      reflectionShiftModel (dozzBase γ μ) ((γ : ℂ) / 2) (2 / γ) (2 / γ) ((Q γ : ℂ) - α) := by
  rw [reflectionDOZZ, show (γ : ℂ) * ((Q γ : ℂ) - α) / 2 = (γ : ℂ) / 2 * ((Q γ : ℂ) - α) by ring,
    show 2 * ((Q γ : ℂ) - α) / γ = (2 / (γ : ℂ)) * ((Q γ : ℂ) - α) by ring]
  rfl

variable {γ : ℝ}

/-- First reflection shift [KRV, (shift1DOZZ)] (correct as printed). -/
theorem reflectionDOZZ_shift_b (hγ : 0 < γ) (hγ2 : γ < 2) {μ : ℝ} (hμ : 0 < μ) :
    ReflectionFirstShift γ μ (reflectionDOZZ γ μ) := by
  let b := (γ : ℂ) / 2
  let c := 2 / (γ : ℂ)
  let B : ℂ := dozzBase γ μ
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hbc : b * c = 1 := by dsimp [b, c]; field_simp
  have hq : b ^ 2 = ((γ ^ 2 / 4 : ℝ) : ℂ) := by dsimp [b]; push_cast; ring
  have hqpos : 0 < γ ^ 2 / 4 := by positivity
  have hqint (n : ℕ) : γ ^ 2 / 4 ≠ (n : ℝ) := by
    have hlt : γ ^ 2 / 4 < 1 := by linarith [pow_lt_pow_left₀ hγ2 hγ.le two_ne_zero]
    cases n with
    | zero => simpa using hqpos.ne'
    | succ n => push_cast; intro hh; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hprod := lFun_real_factors hqpos hqint
  rw [← hq] at hprod
  have hB : B ≠ 0 := ofReal_ne_zero.mpr (reflectionBase_pos hγ hγ2 hμ).ne'
  have hL : lFun (b ^ 2) ≠ 0 := by
    intro h
    have hb : b ≠ 0 := left_ne_zero_of_mul (by rw [hbc]; exact one_ne_zero)
    rw [h, zero_mul] at hprod
    exact div_ne_zero (by norm_num : (-1 : ℂ) ≠ 0)
      (pow_ne_zero _ (pow_ne_zero _ hb)) hprod.symm
  have hbase : B = (μ * Real.pi : ℝ) * lFun (b ^ 2) := by
    have hq' : b ^ 2 = (γ : ℂ) ^ 2 / 4 := by dsimp [b]; ring
    rw [hq', lFun_gammaSq_real]
    dsimp [B, dozzBase]
    rw [lFun_gammaSq_real, Complex.ofReal_re]
    push_cast
    ring
  have hcoef : B ^ (c * b) / lFun (b ^ 2) = (μ * Real.pi : ℝ) := by
    rw [mul_comm c b, hbc, Complex.cpow_one, hbase, mul_div_cancel_right₀ _ hL]
  have hQ : (Q γ : ℂ) = b + c := by simp [Q, b, c, add_comm]
  have hmod (α : ℂ) : reflectionShiftModel B b c c (b + c - α) = reflectionDOZZ γ μ α := by
    rw [← hQ]; exact (reflectionDOZZ_eq_shiftModel γ μ α).symm
  filter_upwards [reflectionShiftModel_step B b c c 0 hbc hB hprod] with α h
  dsimp only at h
  have hmove : b + c - (α + 0) + b = b + c - (α - (γ : ℂ) / 2) := by dsimp [b]; ring
  have harg1 : b * α + b * 0 - b ^ 2 = (γ : ℂ) * α / 2 - (γ : ℂ) ^ 2 / 4 := by dsimp [b]; ring
  have harg2 : 2 + 2 * b ^ 2 - (b * α + b * 0) = 2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * α / 2 := by dsimp [b]; ring
  rw [hmove, add_zero, hmod, hmod, hcoef, harg1, harg2, hq] at h
  simpa only [reflectionFirstShiftDenom, neg_div, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_ofNat] using h

theorem reflectionDOZZ_shift_binv (hγ : 0 < γ) (hγ2 : γ < 2)
    (hγk : ∀ k : ℕ, 4 / γ ^ 2 ≠ (k : ℝ)) {μ : ℝ} (hμ : 0 < μ) :
    ReflectionDualShift γ (reflectionDOZZDualConst γ μ) (reflectionDOZZ γ μ) := by
  let b := (γ : ℂ) / 2
  let c := 2 / (γ : ℂ)
  let B : ℂ := dozzBase γ μ
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hcb : c * b = 1 := by dsimp [b, c]; field_simp
  have hq : c ^ 2 = ((4 / γ ^ 2 : ℝ) : ℂ) := by dsimp [c]; push_cast; ring
  have hprod := lFun_real_factors (show 0 < 4 / γ ^ 2 by positivity) hγk
  rw [← hq] at hprod
  have hB : B ≠ 0 := ofReal_ne_zero.mpr (reflectionBase_pos hγ hγ2 hμ).ne'
  have hQ : (Q γ : ℂ) = c + b := by simp [Q, b, c]
  have hmod (α : ℂ) : reflectionShiftModel B c b c (c + b - α) = reflectionDOZZ γ μ α := by
    rw [reflectionShiftModel_swap, ← hQ]; exact (reflectionDOZZ_eq_shiftModel γ μ α).symm
  filter_upwards [reflectionShiftModel_step B c b c c hcb hB hprod] with α h
  dsimp only at h
  have hmove : c + b - (α + c) + c = c + b - α := by ring
  have harg1 : c * α + c * c - c ^ 2 = 2 * α / (γ : ℂ) := by dsimp [c]; ring
  have harg2 : 2 + 2 * c ^ 2 - (c * α + c * c) = 2 + ((4 / γ ^ 2 : ℝ) : ℂ) - 2 * α / (γ : ℂ) := by
    rw [← hq]; dsimp [c]; ring
  rw [hmove, hmod, hmod, harg1, harg2, ← pow_two, hq] at h
  simpa only [reflectionDOZZDualConst, reflectionDualShiftDenom, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_ofNat, neg_div] using h

end DOZZ.Proofs
