/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.DOZZAlgebra.GenericLocus

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-!
# DOZZ — reflection coefficient shift identities
-/

public section

open Complex Filter Metric Set Topology

namespace DOZZ.Proofs

variable {c d : ℂ} (hc : c ≠ 0)

include c d hc in
private lemma eventually_affine_Gamma_ne_zero  :
    ∀ᶠ α : ℂ in codiscrete ℂ, Complex.Gamma (c * α + d) ≠ 0 := by
  filter_upwards [eventually_affine_ne_neg_nat hc] with α hα
  apply Complex.Gamma_ne_zero
  intro n hn
  exact hα n hn

private lemma lFun_one_sub {z : ℂ} (hz : z ≠ 0) :
    lFun (1 - z) = -z * (Complex.Gamma (-z) / Complex.Gamma z) := by
  have hnum : Complex.Gamma (1 - z) = -z * Complex.Gamma (-z) := by
    calc
      Complex.Gamma (1 - z) = Complex.Gamma (-z + 1) := by congr 1; ring
      _ = -z * Complex.Gamma (-z) :=
        Complex.Gamma_add_one (-z) (neg_ne_zero.mpr hz)
  have hden : 1 - (1 - z) = z := by ring
  unfold lFun
  grind

private lemma lFun_one_add {z : ℂ} (hz : z ≠ 0) :
    lFun (1 + z) = z * (Complex.Gamma z / Complex.Gamma (-z)) := by
  have hnum : Complex.Gamma (1 + z) = z * Complex.Gamma z := by
    calc
      Complex.Gamma (1 + z) = Complex.Gamma (z + 1) := by congr 1; ring
      _ = z * Complex.Gamma z := Complex.Gamma_add_one z hz
  have hden : 1 - (1 + z) = -z := by ring
  unfold lFun
  grind

private lemma eventually_Gamma_Qsub_affine {Q c d : ℂ} (hc : c ≠ 0) :
    ∀ᶠ α : ℂ in codiscrete ℂ, Complex.Gamma (c * (Q - α) + d) ≠ 0 := by
  have h := eventually_affine_Gamma_ne_zero (c := -c) (d := c * Q + d)
    (neg_ne_zero.mpr hc)
  grind

private lemma gamma_ratio_shift_b {t p q : ℂ} (htq : t = q * p)
    (hΓt : Complex.Gamma t ≠ 0) (hΓnegT : Complex.Gamma (-t) ≠ 0)
    (hΓtq : Complex.Gamma (t + q) ≠ 0) (hΓnegTq : Complex.Gamma (-t - q) ≠ 0)
    (hΓp : Complex.Gamma p ≠ 0)
    (hΓp1 : Complex.Gamma (p + 1) ≠ 0) (hΓnegP1 : Complex.Gamma (-p - 1) ≠ 0) :
    (Complex.Gamma (-t - q) / Complex.Gamma (t + q) *
      (Complex.Gamma (-p - 1) / Complex.Gamma (p + 1))) *
        (lFun (1 - t) * lFun (1 + t + q)) =
      q ^ 2 * (Complex.Gamma (-t) / Complex.Gamma t *
        (Complex.Gamma (-p) / Complex.Gamma p)) := by
  have ht : t ≠ 0 := by
    intro h
    simp [h] at hΓt
  have htq' : t + q ≠ 0 := by
    intro h
    simp [h] at hΓtq
  have hp : p ≠ 0 := by
    intro h
    simp [h] at hΓp
  have hp1 : p + 1 ≠ 0 := by
    intro h
    simp [h] at hΓp1
  have hrecN : Complex.Gamma (-p) = (-p - 1) * Complex.Gamma (-p - 1) := by
    have hzero : -p - 1 ≠ 0 := by
      intro h
      simp [h] at hΓnegP1
    have harg : (-p - 1) + 1 = -p := by ring
    grind
  have hrecP  := Complex.Gamma_add_one p hp
  have harg : 1 + t + q = 1 + (t + q) := by ring
  rw [lFun_one_sub ht, harg, lFun_one_add htq', hrecN, hrecP]
  rw [show -(t + q) = -t - q by ring]
  field_simp [hΓt, hΓnegT, hΓtq, hΓnegTq, hΓp, hΓp1, hΓnegP1,
    hp, hp1, ht, htq']
  rw [htq]
  ring

private lemma complexGamma_neg_sq_ne_zero {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    Complex.Gamma (-((γ : ℂ) ^ 2 / 4)) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro n hn
  have hq : γ ^ 2 / 4 = (n : ℝ) := by
    have hreal : - (γ ^ 2 / 4) = -(n : ℝ) := by exact_mod_cast hn
    exact neg_inj.mp hreal
  have hγsq_pos : 0 < γ ^ 2 / 4 := by positivity
  have hγsq_lt : γ ^ 2 / 4 < 1 := by nlinarith
  simp_all

variable {γ : ℝ}

/-- First reflection shift [KRV, (shift1DOZZ)] (correct as printed). -/
theorem reflectionDOZZ_shift_b (hγ : 0 < γ) (hγ2 : γ < 2) {μ : ℝ} (hμ : 0 < μ) :
    ∀ᶠ α in codiscrete ℂ,
      reflectionDOZZ γ μ (α - γ / 2) =
        -(μ * Real.pi) * reflectionDOZZ γ μ α /
          (lFun (-(γ ^ 2 / 4)) * lFun (γ * α / 2 - γ ^ 2 / 4) * lFun (2 + γ ^ 2 / 2 - γ * α / 2)) := by
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hqRpos : 0 < γ ^ 2 / 4 := by positivity
  have hqRlt : γ ^ 2 / 4 < 1 := by
    nlinarith
  let qR  := γ ^ 2 / 4
  let q  := (γ : ℂ) ^ 2 / 4
  let b  := (γ : ℂ) / 2
  let c  := 2 / (γ : ℂ)
  let Qc  := (Q γ : ℂ)
  have hqCast : (qR : ℂ) = q := by
    dsimp [q, qR]
    push_cast
    ring
  have hqpos : 0 < qR := hqRpos
  have hΓq : Complex.Gamma q ≠ 0 := by
    rw [← hqCast, Complex.Gamma_ofReal]
    exact_mod_cast (Real.Gamma_pos_of_pos hqpos).ne'
  have hΓ1q : Complex.Gamma (1 + q) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    rw [add_re, one_re]
    rw [← hqCast]
    simp only [Complex.ofReal_re]
    linarith
  have hqArg : (qR : ℂ) = (γ : ℂ) ^ 2 / 4 := by
    dsimp [qR]
    push_cast
    ring
  have hΓnegq : Complex.Gamma (-q) ≠ 0 := complexGamma_neg_sq_ne_zero hγ hγ2
  have hqne : q ≠ 0 := by
    continuity
  have hLneg : lFun (-q) ≠ 0 := by
    unfold lFun
    simp_all
  have hLprod := lFun_mul_neg hqne hΓq hΓnegq
  have hLreal := lFun_gammaSq_real γ
  have hbase := dozzBase_pos hγ hγ2 hμ
  let B : ℂ := (dozzBase γ μ : ℝ)
  let C : ℂ := (μ * Real.pi : ℝ)
  have hbaseEq : B = C * lFun q := by
    change ((Real.pi * μ * (lFun q).re : ℝ) : ℂ) = _
    rw [hLreal]
    simp only [Complex.ofReal_re]
    change ((Real.pi * μ *
      (Real.Gamma (γ ^ 2 / 4) / Real.Gamma (1 - γ ^ 2 / 4)) : ℝ) : ℂ) =
      ((μ * Real.pi : ℝ) : ℂ) *
        ((Real.Gamma (γ ^ 2 / 4) / Real.Gamma (1 - γ ^ 2 / 4) : ℝ) : ℂ)
    push_cast
    ring
  have hcoeff : B * q ^ 2 = -C / lFun (-q) := by
    grind
  have hb : b ≠ 0 := by
    continuity
  have hc : c ≠ 0 := by
    continuity
  have hT := eventually_Gamma_Qsub_affine (Q := Qc) (c := b) (d := 0) hb
  have hNegT := eventually_Gamma_Qsub_affine (Q := Qc) (c := -b) (d := 0)
    (neg_ne_zero.mpr hb)
  have hTq := eventually_Gamma_Qsub_affine (Q := Qc) (c := b) (d := q) hb
  have hNegTq := eventually_Gamma_Qsub_affine (Q := Qc) (c := -b) (d := -q)
    (neg_ne_zero.mpr hb)
  have hP := eventually_Gamma_Qsub_affine (Q := Qc) (c := c) (d := 0) hc
  have hP1 := eventually_Gamma_Qsub_affine (Q := Qc) (c := c) (d := 1) hc
  have hNegP1 := eventually_Gamma_Qsub_affine (Q := Qc) (c := -c) (d := -1)
    (neg_ne_zero.mpr hc)
  have hOneSubT := eventually_Gamma_Qsub_affine (Q := Qc) (c := -b) (d := 1)
    (neg_ne_zero.mpr hb)
  have hOnePlusTq := eventually_Gamma_Qsub_affine (Q := Qc) (c := b) (d := 1 + q) hb
  filter_upwards [hT, hNegT, hTq, hNegTq, hP, hP1, hNegP1, hOneSubT, hOnePlusTq]
      with α hT hNegT hTq hNegTq hP hP1 hNegP1 hOneSubT hOnePlusTq
  let A  := Qc - α
  let t  := b * A
  let p  := c * A
  have hΓt : Complex.Gamma t ≠ 0 := by simpa [t, A] using hT
  have hΓnegT : Complex.Gamma (-t) ≠ 0 := by simpa [t, A] using hNegT
  have hΓtq : Complex.Gamma (t + q) ≠ 0 := hTq
  have hΓnegTq : Complex.Gamma (-t - q) ≠ 0 := by
    grind
  have hΓp : Complex.Gamma p ≠ 0 := by simpa [p, A] using hP
  have hΓp1 : Complex.Gamma (p + 1) ≠ 0 := hP1
  have hΓnegP1 : Complex.Gamma (-p - 1) ≠ 0 := by
    grind
  have hΓ1subT : Complex.Gamma (1 - t) ≠ 0 := by
    grind
  have hΓ1plusTq : Complex.Gamma (1 + t + q) ≠ 0 := by
    grind
  have htq : t = q * p := by
    grind


  have hL1 : lFun (1 - t) ≠ 0 := by
    unfold lFun
    grind
  have hL2 : lFun (1 + t + q) ≠ 0 := by
    unfold lFun
    grind
  have hAshift : Qc - (α - b) = A + b := by
    dsimp [A]
    ring
  have hExp : 2 * A / (γ : ℂ) = p := by
    dsimp [p, c]
    field_simp [hγc]
  have hTarg : (γ : ℂ) * A / 2 = t := by
    dsimp [t, b]
    ring
  have hExpShift : 2 * (Qc - (α - b)) / (γ : ℂ) = p + 1 := by
    grind
  have hTargShift : (γ : ℂ) * (Qc - (α - b)) / 2 = t + q := by
    rw [hAshift]
    dsimp [t, b, q]
    ring
  have htFormula : t = 1 + q - (γ : ℂ) * α / 2 := by
    dsimp [t, b, A, Qc, q]
    rw [show (Q γ : ℂ) = 2 / (γ : ℂ) + (γ : ℂ) / 2 by simp [Q]]
    field_simp [hγc]
    ring
  have hLarg1 : (γ : ℂ) * α / 2 - q = 1 - t := by rw [htFormula]; ring
  have hLarg2 : 2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * α / 2 = 1 + t + q := by
    rw [htFormula]
    ring
  have hExp' : 2 * ((Q γ : ℂ) - α) / (γ : ℂ) = p := hExp
  have hTarg' : (γ : ℂ) * ((Q γ : ℂ) - α) / 2 = t := hTarg
  have hExpShift' :
      2 * ((Q γ : ℂ) - (α - (γ : ℂ) / 2)) / (γ : ℂ) = p + 1 := hExpShift
  have hTargShift' :
      (γ : ℂ) * ((Q γ : ℂ) - (α - (γ : ℂ) / 2)) / 2 = t + q := hTargShift
  have hpow : B ^ (p + 1) = B * B ^ p := by
    have hBne : B ≠ 0 := by
      dsimp [B]
      exact_mod_cast hbase.ne'
    rw [Complex.cpow_add p 1 hBne]
    simp only [Complex.cpow_one]
    ring
  let Gshift  := Complex.Gamma (-t - q) / Complex.Gamma (t + q) *
    (Complex.Gamma (-p - 1) / Complex.Gamma (p + 1))
  let Gold  := Complex.Gamma (-t) / Complex.Gamma t *
    (Complex.Gamma (-p) / Complex.Gamma p)
  have hratio := gamma_ratio_shift_b htq hΓt hΓnegT hΓtq hΓnegTq hΓp hΓp1 hΓnegP1
  have hratio' : Gshift * (lFun (1 - t) * lFun (1 + t + q)) = q ^ 2 * Gold := hratio
  have hscaled : (B * Gshift) * (lFun (-q) * lFun (1 - t) * lFun (1 + t + q)) =
      -C * Gold := by
    calc
      _ = (B * lFun (-q)) * (Gshift * (lFun (1 - t) * lFun (1 + t + q))) := by ring
      _ = (B * lFun (-q)) * (q ^ 2 * Gold) := by
        rw [hratio']
      _ = (B * q ^ 2) * lFun (-q) * Gold := by ring
      _ = _ := by rw [hcoeff]; field_simp [hLneg]
  have hden  :=
    mul_ne_zero (mul_ne_zero hLneg hL1) hL2
  have hleft :
      reflectionDOZZ γ μ (α - γ / 2) = -B ^ (p + 1) * Gshift := by
    have hnegTq : -(t + q) = -t - q := by ring
    have hnegP1 : -(p + 1) = -p - 1 := by ring
    simp only [reflectionDOZZ, hExpShift', hTargShift', hnegTq, hnegP1, Gshift, B]
    ring
  have hright :
      reflectionDOZZ γ μ α = -B ^ p * Gold := by
    simp only [reflectionDOZZ, hExp', hTarg', Gold, B]
    ring
  have hfinal :
      reflectionDOZZ γ μ (α - γ / 2) =
        -C * reflectionDOZZ γ μ α /
          (lFun (-q) * lFun (1 - t) * lFun (1 + t + q)) := by
    apply (eq_div_iff hden).2
    rw [hleft, hright, hpow]
    calc
      -(B * B ^ p) * Gshift * (lFun (-q) * lFun (1 - t) * lFun (1 + t + q)) =
        -B ^ p * ((B * Gshift) * (lFun (-q) * lFun (1 - t) * lFun (1 + t + q))) := by ring
      _ = -B ^ p * (-C * Gold) := by rw [hscaled]
      _ = -C * (-B ^ p * Gold) := by ring
  simpa [q, C, hLarg1, hLarg2, Complex.ofReal_mul] using hfinal

private lemma gamma_ratio_shift_binv {t p N : ℂ} (htN : t * N = p)
    (hΓt : Complex.Gamma t ≠ 0) (hΓnegT : Complex.Gamma (-t) ≠ 0)
    (hΓtm1 : Complex.Gamma (t - 1) ≠ 0)
    (hΓp : Complex.Gamma p ≠ 0) (hΓnegP : Complex.Gamma (-p) ≠ 0)
    (hΓpmN : Complex.Gamma (p - N) ≠ 0) (hΓNmp : Complex.Gamma (N - p) ≠ 0) :
    (Complex.Gamma (-t) / Complex.Gamma t *
      (Complex.Gamma (-p) / Complex.Gamma p)) *
        (lFun (1 + N - p) * lFun (1 + p)) =
      N ^ 2 * (Complex.Gamma (1 - t) / Complex.Gamma (t - 1) *
        (Complex.Gamma (N - p) / Complex.Gamma (p - N))) := by
  have ht : t ≠ 0 := by
    intro h
    simp [h] at hΓt
  have htm1 : t - 1 ≠ 0 := by
    intro h
    simp [h] at hΓtm1
  have hp : p ≠ 0 := by
    intro h
    simp [h] at hΓp
  have hNmp : N - p ≠ 0 := by
    intro h
    simp [h] at hΓNmp
  have hrecTm : Complex.Gamma (1 - t) = -t * Complex.Gamma (-t) := by
    simpa [sub_eq_add_neg, add_comm] using
      Complex.Gamma_add_one (-t) (neg_ne_zero.mpr ht)
  have hrecT : Complex.Gamma t = (t - 1) * Complex.Gamma (t - 1) := by
    have harg : t - 1 + 1 = t := by ring
    grind
  have harg : 1 + N - p = 1 + (N - p) := by ring
  rw [harg, lFun_one_add hNmp, lFun_one_add hp, hrecTm, hrecT]
  grind

theorem reflectionDOZZ_shift_binv (hγ : 0 < γ) (hγ2 : γ < 2)
    (hγk : ∀ k : ℕ, 4 / γ ^ 2 ≠ (k : ℝ)) {μ : ℝ} (hμ : 0 < μ) :
    ∀ᶠ α in codiscrete ℂ,
      reflectionDOZZ γ μ α =
        -(((dozzBase γ μ : ℝ) : ℂ) ^ ((4 / γ ^ 2 : ℝ) : ℂ) / lFun ((4 / γ ^ 2 : ℝ) : ℂ)) *
          reflectionDOZZ γ μ (α + 2 / γ) /
          (lFun (-((4 / γ ^ 2 : ℝ) : ℂ)) * lFun (2 * α / γ) * lFun (2 + (4 / γ ^ 2 : ℝ) - 2 * α / γ)) := by
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'

  have hbase := dozzBase_pos hγ hγ2 hμ
  let B : ℂ := (dozzBase γ μ : ℝ)
  let NR  := 4 / γ ^ 2
  let N  := (NR : ℂ)
  have hNRpos : 0 < NR := by dsimp [NR]; positivity
  have hNne : N ≠ 0 := by
    dsimp [N]
    exact_mod_cast hNRpos.ne'

  have hNcomplex : N = 4 / (γ : ℂ) ^ 2 := by
    continuity
  have hΓN : Complex.Gamma N ≠ 0 := by
    dsimp [N]
    rw [Complex.Gamma_ofReal]
    exact_mod_cast (Real.Gamma_pos_of_pos hNRpos).ne'
  have hΓnegN : Complex.Gamma (-N) ≠ 0 := by
    dsimp [N]
    apply Complex.Gamma_ne_zero
    intro k hk
    have hval : NR = (k : ℝ) := by
      have hreal : -NR = -(k : ℝ) := by exact_mod_cast hk
      linarith
    continuity
  have hΓ1subN : Complex.Gamma (1 - N) ≠ 0 := by
    dsimp [N]
    apply Complex.Gamma_ne_zero
    intro k hk
    have hval : NR = (k + 1 : ℝ) := by
      have hreal : 1 - NR = -(k : ℝ) := by exact_mod_cast hk
      linarith
    have hval' : 4 / γ ^ 2 = ((k + 1 : ℕ) : ℝ) := by
      simpa [NR] using hval
    exact hγk (k + 1) hval'
  have hΓ1plusN : Complex.Gamma (1 + N) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    rw [add_re, one_re]
    dsimp [N]
    linarith
  have hLN : lFun N ≠ 0 := div_ne_zero hΓN hΓ1subN
  have hLnegN : lFun (-N) ≠ 0 := by
    unfold lFun
    simp_all
  have hLprodN := lFun_mul_neg hNne hΓN hΓnegN
  have hb : (γ : ℂ) / 2 ≠ 0 := div_ne_zero hγc (by norm_num)
  have hc : (2 : ℂ) / (γ : ℂ) ≠ 0 := div_ne_zero (by norm_num) hγc
  let b  := (γ : ℂ) / 2
  let c  := (2 : ℂ) / (γ : ℂ)
  let Qc  := (Q γ : ℂ)
  have hT := eventually_Gamma_Qsub_affine (Q := Qc) (c := b) (d := 0) hb
  have hNegT := eventually_Gamma_Qsub_affine (Q := Qc) (c := -b) (d := 0)
    (neg_ne_zero.mpr hb)
  have hTm1 := eventually_Gamma_Qsub_affine (Q := Qc) (c := b) (d := -1) hb
  have hOneSubT := eventually_Gamma_Qsub_affine (Q := Qc) (c := -b) (d := 1)
    (neg_ne_zero.mpr hb)
  have hP := eventually_Gamma_Qsub_affine (Q := Qc) (c := c) (d := 0) hc
  have hNegP := eventually_Gamma_Qsub_affine (Q := Qc) (c := -c) (d := 0)
    (neg_ne_zero.mpr hc)
  have hPmN := eventually_Gamma_Qsub_affine (Q := Qc) (c := c) (d := -N) hc
  have hNmp := eventually_Gamma_Qsub_affine (Q := Qc) (c := -c) (d := N)
    (neg_ne_zero.mpr hc)
  have hOnePlusNmp := eventually_Gamma_Qsub_affine (Q := Qc) (c := -c) (d := 1 + N)
    (neg_ne_zero.mpr hc)
  have hOnePlusP := eventually_Gamma_Qsub_affine (Q := Qc) (c := c) (d := 1) hc
  filter_upwards [hT, hNegT, hTm1, hOneSubT, hP, hNegP, hPmN, hNmp,
      hOnePlusNmp, hOnePlusP]
      with α hT hNegT hTm1 hOneSubT hP hNegP hPmN hNmp hOnePlusNmp hOnePlusP
  let A  := Qc - α
  let t  := b * A
  let p  := c * A
  have hΓt : Complex.Gamma t ≠ 0 := by simpa [t, A] using hT
  have hΓnegT : Complex.Gamma (-t) ≠ 0 := by simpa [t, A] using hNegT
  have hΓtm1 : Complex.Gamma (t - 1) ≠ 0 := by
    bound
  have hΓp : Complex.Gamma p ≠ 0 := by simpa [p, A] using hP
  have hΓnegP : Complex.Gamma (-p) ≠ 0 := by simpa [p, A] using hNegP
  have hΓpmN : Complex.Gamma (p - N) ≠ 0 := by
    bound
  have hΓNmp : Complex.Gamma (N - p) ≠ 0 := by
    grind
  have hΓ1subT : Complex.Gamma (1 - t) ≠ 0 := by
    grind
  have hΓ1plusNmp : Complex.Gamma (1 + N - p) ≠ 0 := by
    grind
  have hΓ1plusP : Complex.Gamma (1 + p) ≠ 0 := by
    simpa [p, A, add_comm] using hOnePlusP
  have htN : t * N = p := by
    dsimp [t, p, A, b, c]
    rw [hNcomplex]
    field_simp [hγc]
    ring
  have hL1 : lFun (1 + N - p) ≠ 0 := by
    unfold lFun
    grind
  have hL2 : lFun (1 + p) ≠ 0 := by
    unfold lFun
    grind
  have hAshift : Qc - (α + c) = A - c := by dsimp [A]; ring
  have hExp : 2 * A / (γ : ℂ) = p := by
    dsimp [p, c]
    field_simp [hγc]
  have hTarg : (γ : ℂ) * A / 2 = t := by dsimp [t, b]; ring
  have hExpShift : 2 * (Qc - (α + c)) / (γ : ℂ) = p - N := by
    rw [hAshift]
    calc
      2 * (A - c) / (γ : ℂ) = 2 * A / (γ : ℂ) - 2 * c / (γ : ℂ) := by ring
      _ = p - N := by
        rw [hExp]
        have hcN : 2 * c / (γ : ℂ) = N := by
          dsimp [c]
          rw [hNcomplex]
          field_simp [hγc]
          norm_num
        rw [hcN]
  have hTargShift : (γ : ℂ) * (Qc - (α + c)) / 2 = t - 1 := by
    grind
  have hQc : (Q γ : ℂ) = 2 / (γ : ℂ) + (γ : ℂ) / 2 := by simp [Q]
  have hpFormula : p = 1 + N - 2 * α / (γ : ℂ) := by
    grind
  have hLarg1 : 2 * α / (γ : ℂ) = 1 + N - p := by rw [hpFormula]; ring
  have hLarg2 : 2 + N - 2 * α / (γ : ℂ) = 1 + p := by rw [hpFormula]; ring
  have hExp' : 2 * ((Q γ : ℂ) - α) / (γ : ℂ) = p := hExp
  have hTarg' : (γ : ℂ) * ((Q γ : ℂ) - α) / 2 = t := hTarg
  have hcCast : ((2 / γ : ℝ) : ℂ) = c := by
    dsimp [c]
    push_cast
    field_simp [hγc]
  have hExpShift' :
      2 * ((Q γ : ℂ) - (α + (2 : ℂ) / (γ : ℂ))) / (γ : ℂ) = p - N := hExpShift
  have hTargShift' :
      (γ : ℂ) * ((Q γ : ℂ) - (α + (2 : ℂ) / (γ : ℂ))) / 2 = t - 1 := hTargShift
  have hBne : B ≠ 0 := by
    dsimp [B]
    exact_mod_cast hbase.ne'
  have hpow : B ^ p = B ^ N * B ^ (p - N) := by
    calc
      B ^ p = B ^ (N + (p - N)) := by congr 1; ring
      _ = B ^ N * B ^ (p - N) := Complex.cpow_add N (p - N) hBne
  let Gorig  := Complex.Gamma (-t) / Complex.Gamma t *
    (Complex.Gamma (-p) / Complex.Gamma p)
  let Gshift  := Complex.Gamma (1 - t) / Complex.Gamma (t - 1) *
    (Complex.Gamma (N - p) / Complex.Gamma (p - N))
  have hratio := gamma_ratio_shift_binv htN hΓt hΓnegT hΓtm1 hΓp hΓnegP hΓpmN hΓNmp
  have hratio' : Gorig * (lFun (1 + N - p) * lFun (1 + p)) = N ^ 2 * Gshift := hratio
  have hden  :=
    mul_ne_zero (mul_ne_zero hLnegN hL1) hL2
  have hscaled : Gorig * (lFun N * lFun (-N) *
      lFun (1 + N - p) * lFun (1 + p)) = -Gshift := by
    calc
      _ = (Gorig * (lFun (1 + N - p) * lFun (1 + p))) *
          (lFun N * lFun (-N)) := by ring
      _ = (N ^ 2 * Gshift) * (lFun N * lFun (-N)) := by rw [hratio']
      _ = -Gshift := by rw [hLprodN]; field_simp [hNne]
  have hGammaCoeff :
      -Gorig * (lFun (-N) * lFun (1 + N - p) * lFun (1 + p)) = Gshift / lFun N := by
    apply (eq_div_iff hLN).2
    calc
      (-Gorig * (lFun (-N) * lFun (1 + N - p) * lFun (1 + p))) * lFun N =
          -(Gorig * (lFun N * lFun (-N) * lFun (1 + N - p) * lFun (1 + p))) := by ring
      _ = Gshift := by rw [hscaled]; ring
  have hnegTm1 : -(t - 1) = 1 - t := by ring
  have hnegPmN : -(p - N) = N - p := by ring
  have hleft : reflectionDOZZ γ μ (α + 2 / γ) = -B ^ (p - N) * Gshift := by
    simp only [reflectionDOZZ, hExpShift', hTargShift', hnegTm1, hnegPmN, Gshift, B]
    ring
  have hright : reflectionDOZZ γ μ α = -B ^ p * Gorig := by
    simp only [reflectionDOZZ, hExp', hTarg', Gorig, B]
    ring
  grind

end DOZZ.Proofs
