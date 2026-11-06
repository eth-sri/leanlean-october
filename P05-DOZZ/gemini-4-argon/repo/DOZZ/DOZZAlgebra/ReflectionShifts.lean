/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Topology.MetricSpace.Basic

/-!
# DOZZ — reflection coefficient shift identities
-/

@[expose] public section

open Complex Filter Metric Set Topology

namespace DOZZ.Proofs

private lemma closedEmbedding_affine_nat {c d} (hc : c ≠ 0) :
    IsClosedEmbedding (fun n : ℕ => c * (n : ℂ) + d) := by
  apply Metric.isClosedEmbedding_of_pairwise_le_dist (norm_pos_iff.mpr hc)
  intro m n hmn
  rw [dist_eq_norm]
  calc
    ‖c‖ = ‖c‖ * 1 := by ring
    _ ≤ ‖c‖ * |(m : ℝ) - n| := mul_le_mul_of_nonneg_left (by simpa only [Nat.dist_eq] using (Nat.pairwise_one_le_dist hmn)) (norm_nonneg _)
    _ = ‖c * ((m : ℂ) - n)‖ := by rw [norm_mul, (show ‖(m : ℂ) - n‖ = |(m : ℝ) - n| by rw [(show (m : ℂ) - (n : ℂ) = (((m : ℝ) - n : ℝ) : ℂ) by push_cast; ring), Complex.norm_real, Real.norm_eq_abs])]
    _ = ‖c * (m : ℂ) + d - (c * n + d)‖ := by congr 1; ring

private lemma eventually_affine_ne_neg_nat {c d} (hc : c ≠ 0) :
    ∀ᶠ α : ℂ in codiscrete ℂ, ∀ n : ℕ, c * α + d ≠ -(n : ℂ) := by
  let f : ℕ → ℂ := fun n => -(c⁻¹) * (n : ℂ) - d / c
  have hf : IsClosedEmbedding f := by
    simpa [f, sub_eq_add_neg, neg_div] using closedEmbedding_affine_nat (c := -(c⁻¹)) (d := -d / c)
      (neg_ne_zero.mpr (inv_ne_zero hc))
  filter_upwards [(by apply compl_mem_codiscrete_iff.mpr; exact ⟨hf.isClosed_range, hf.isEmbedding.isInducing.isDiscrete_range⟩)] with α hα n
  intro heq
  apply hα
  refine ⟨n, ?_⟩
  have hsolve : α = f n := by
    calc
      α = (-(n : ℂ) - d) / c := by
        apply (eq_div_iff hc).2
        calc
          α * c = c * α := mul_comm _ _
          _ = -(n : ℂ) - d := by linear_combination heq
      _ = f n := by
        dsimp [f]
        field_simp [hc]
  exact hsolve.symm



private lemma lFun_one_add {z} (hz : z ≠ 0) :
    lFun (1 + z) = z * (Complex.Gamma z / Complex.Gamma (-z)) := by
  have hnum : Complex.Gamma (1 + z) = z * Complex.Gamma z := by
    calc
      Complex.Gamma (1 + z) = Complex.Gamma (z + 1) := by congr 1; ring
      _ = z * Complex.Gamma z := Complex.Gamma_add_one z hz
  unfold lFun
  rw [hnum, (show 1 - (1 + z) = -z by ring)]
  simp only [div_eq_mul_inv]
  ring

private lemma eventually_Gamma_Qsub_affine {Q c d} (hc : c ≠ 0) :
    ∀ᶠ α : ℂ in codiscrete ℂ, Complex.Gamma (c * (Q - α) + d) ≠ 0 := by
  have eventually_affine_Gamma_ne_zero {c} {d} (hc : c ≠ 0) : ∀ᶠ α : ℂ in codiscrete ℂ, Complex.Gamma (c * α + d) ≠ 0 := by
    filter_upwards [eventually_affine_ne_neg_nat hc] with α hα
    apply Complex.Gamma_ne_zero
    intro n hn
    exact hα n hn
  filter_upwards [(eventually_affine_Gamma_ne_zero (c := -c) (d := c * Q + d) (neg_ne_zero.mpr hc))] with α hα
  rw [(show c * (Q - α) + d = -c * α + (c * Q + d) by ring)]
  exact hα

private lemma lFun_mul_neg {q} (hq : q ≠ 0)
    (hΓq : Complex.Gamma q ≠ 0) (hΓnegq : Complex.Gamma (-q) ≠ 0) :
    lFun q * lFun (-q) = -1 / q ^ 2 := by
  unfold lFun
  rw [(show Complex.Gamma (1 - q) = -q * Complex.Gamma (-q) by simpa [sub_eq_add_neg, add_comm] using Complex.Gamma_add_one (-q) (neg_ne_zero.mpr hq)), show 1 - -q = 1 + q by simp, (show Complex.Gamma (1 + q) = q * Complex.Gamma q by simpa [add_comm] using Complex.Gamma_add_one q hq)]
  field_simp [hq, hΓq, hΓnegq]


private lemma lFun_gammaSq_real (γ : ℝ) :
    lFun ((γ : ℂ) ^ 2 / 4) =
      ((Real.Gamma (γ ^ 2 / 4) / Real.Gamma (1 - γ ^ 2 / 4) : ℝ) : ℂ) := by
  rw [(show ((γ : ℂ) ^ 2 / 4) = ((γ ^ 2 / 4 : ℝ) : ℂ) by push_cast; ring)]
  unfold lFun
  rw [Complex.Gamma_ofReal, (show Complex.Gamma (1 - (γ ^ 2 / 4 : ℝ)) = (Real.Gamma (1 - γ ^ 2 / 4) : ℂ) by convert Complex.Gamma_ofReal (1 - γ ^ 2 / 4) using 1; simp)]
  exact (Complex.ofReal_div _ _).symm

private lemma complexGamma_neg_sq_ne_zero {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    Complex.Gamma (-((γ : ℂ) ^ 2 / 4)) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro n hn
  have hq : γ ^ 2 / 4 = (n : ℝ) := neg_inj.mp (by exact_mod_cast hn)
  have : 0 < γ ^ 2 / 4 := by positivity
  have : γ ^ 2 / 4 < 1 := by linarith only [pow_lt_pow_left₀ hγ2 hγ.le two_ne_zero]
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst n
    norm_num at hq
    linarith
  · have hnle : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
    linarith

variable {γ : ℝ}

/-- First reflection shift [KRV, (shift1DOZZ)] (correct as printed). -/
theorem reflectionDOZZ_shift_b (hγ : 0 < γ) (hγ2 : γ < 2) {μ} (hμ : 0 < μ) :
    ∀ᶠ α in codiscrete ℂ,
      reflectionDOZZ γ μ (α - γ / 2) =
        -(μ * Real.pi) * reflectionDOZZ γ μ α /
          (lFun (-(γ ^ 2 / 4)) * lFun (γ * α / 2 - γ ^ 2 / 4) * lFun (2 + γ ^ 2 / 2 - γ * α / 2)) := by
  have gamma_ratio_shift_b {t} {p} {q} (htq : t = q * p) (hΓt : Complex.Gamma t ≠ 0) (hΓnegT : Complex.Gamma (-t) ≠ 0) (hΓtq : Complex.Gamma (t + q) ≠ 0) (hΓnegTq : Complex.Gamma (-t - q) ≠ 0) (hΓp : Complex.Gamma p ≠ 0) (hΓp1 : Complex.Gamma (p + 1) ≠ 0) (hΓnegP1 : Complex.Gamma (-p - 1) ≠ 0) : (Complex.Gamma (-t - q) / Complex.Gamma (t + q) * (Complex.Gamma (-p - 1) / Complex.Gamma (p + 1))) * (lFun (1 - t) * lFun (1 + t + q)) = q ^ 2 * (Complex.Gamma (-t) / Complex.Gamma t * (Complex.Gamma (-p) / Complex.Gamma p)) := by
    have lFun_one_sub {z} (hz : z ≠ 0) : lFun (1 - z) = -z * (Complex.Gamma (-z) / Complex.Gamma z) := by
      have hnum : Complex.Gamma (1 - z) = -z * Complex.Gamma (-z) := by
        calc
          Complex.Gamma (1 - z) = Complex.Gamma (-z + 1) := by congr 1; ring
          _ = -z * Complex.Gamma (-z) :=
            Complex.Gamma_add_one (-z) (neg_ne_zero.mpr hz)
      unfold lFun
      rw [hnum, (show 1 - (1 - z) = z by ring)]
      simp only [div_eq_mul_inv]
      ring
    have ht : t ≠ 0 := by
      intro h
      simp [h] at hΓt
    have htq' : t + q ≠ 0 := by
      intro h
      simp [h] at hΓtq
    have hp : p ≠ 0 := by
      intro h
      simp [h] at hΓp
    have hrecN : Complex.Gamma (-p) = (-p - 1) * Complex.Gamma (-p - 1) := by
      calc
        Complex.Gamma (-p) = Complex.Gamma ((-p - 1) + 1) :=
          congrArg Complex.Gamma (show (-p - 1) + 1 = -p by ring).symm
        _ = (-p - 1) * Complex.Gamma (-p - 1) :=
          Complex.Gamma_add_one (-p - 1) (by intro h; simp [h] at hΓnegP1)
    have hΓtq' : Complex.Gamma (q * p + q) ≠ 0 := by
      simpa [htq] using hΓtq
    have hΓnegTq' : Complex.Gamma (-q - q * p) ≠ 0 := by
      rw [(show -q - q * p = -t - q by rw [htq]; ring)]
      exact hΓnegTq
    have hΓqp1 : Complex.Gamma (q * (p + 1)) ≠ 0 := by
      rw [(show q * (p + 1) = q * p + q by ring)]
      exact hΓtq'
    have hΓnegqp1 : Complex.Gamma (-(q * (p + 1))) ≠ 0 := by
      rw [(show -(q * (p + 1)) = -q - q * p by ring)]
      exact hΓnegTq'
    rw [lFun_one_sub ht, (show 1 + t + q = 1 + (t + q) by ring), lFun_one_add htq', hrecN, (Complex.Gamma_add_one p hp), htq]
    field_simp [(show Complex.Gamma (q * p) ≠ 0 by simpa [htq] using hΓt), (by simpa [htq] using hΓnegT), hΓtq', hΓnegTq', hΓp, hΓp1, hΓnegP1,
      hΓqp1, hΓnegqp1, hp, (show p + 1 ≠ 0 by intro h; simp [h] at hΓp1), ht, htq']
    rw [show q * (-p - 1) = -(q * (p + 1)) by ring]
    field_simp [hΓqp1, hΓnegqp1]
    ring
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hqRpos : 0 < γ ^ 2 / 4 := by positivity
  have : γ ^ 2 / 4 < 1 := by
    linarith only [pow_lt_pow_left₀ hγ2 hγ.le two_ne_zero]
  let qR : ℝ := γ ^ 2 / 4
  let q : ℂ := (γ : ℂ) ^ 2 / 4
  let b := (γ : ℂ) / 2
  let c := 2 / (γ : ℂ)
  let Qc := (Q γ : ℂ)
  have hqCast : (qR : ℂ) = q := by
    dsimp [q, qR]
    push_cast
    ring
  have hqpos : 0 < qR := hqRpos
  have hΓ1q : Complex.Gamma (1 + q) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    rw [add_re, one_re, ← hqCast]
    simp only [Complex.ofReal_re]
    linarith
  have hqArg : (qR : ℂ) = (γ : ℂ) ^ 2 / 4 := by
    dsimp [qR]
    push_cast
    ring
  have hΓnegq : Complex.Gamma (-q) ≠ 0 := by
    rw [← hqCast, hqArg]
    exact complexGamma_neg_sq_ne_zero hγ hγ2
  have hqne : q ≠ 0 := by
    dsimp [q]
    exact div_ne_zero (pow_ne_zero 2 hγc) (by norm_num)
  have hLneg : lFun (-q) ≠ 0 := by
    unfold lFun
    apply div_ne_zero hΓnegq
    rw [show 1 - -q = 1 + q by ring]
    exact hΓ1q
  have hLreal := lFun_gammaSq_real γ
  let B : ℂ := (dozzBase γ μ : ℝ)
  let C := (μ * Real.pi : ℝ)
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
    apply (eq_div_iff hLneg).2
    rw [hbaseEq]
    calc
      C * lFun q * q ^ 2 * lFun (-q) = C * (lFun q * lFun (-q)) * q ^ 2 := by ring
      _ = C * (-1 / q ^ 2) * q ^ 2 := by rw [(lFun_mul_neg hqne (show Complex.Gamma q ≠ 0 by rw [← hqCast, Complex.Gamma_ofReal]; exact_mod_cast (Real.Gamma_pos_of_pos hqpos).ne') hΓnegq)]
      _ = -C := by field_simp [hqne]
  have hb : b ≠ 0 := by
    dsimp [b]
    exact div_ne_zero hγc (by norm_num)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact div_ne_zero (by norm_num) hγc
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
  let A := Qc - α
  let t : ℂ := b * A
  let p : ℂ := c * A
  have hΓt : Complex.Gamma t ≠ 0 := by simpa [t, A] using hT
  have hΓnegTq : Complex.Gamma (-t - q) ≠ 0 := by
    simpa [t, A, sub_eq_add_neg, add_comm] using hNegTq
  have hAshift : Qc - (α - b) = A + b := by
    dsimp [A]
    ring
  have htFormula : t = 1 + q - (γ : ℂ) * α / 2 := by
    dsimp [t, b, A, Qc, q]
    rw [show (Q γ : ℂ) = 2 / (γ : ℂ) + (γ : ℂ) / 2 by simp [Q]]
    field_simp [hγc]
    ring
  have hpow : B ^ (p + 1) = B * B ^ p := by
    rw [Complex.cpow_add p 1 (show B ≠ 0 by dsimp [B]; exact_mod_cast (show 0 < dozzBase γ μ by rw [dozzBase]; exact mul_pos (mul_pos Real.pi_pos hμ) (show 0 < (lFun q).re by rw [hLreal, Complex.ofReal_re]; exact div_pos (Real.Gamma_pos_of_pos hqRpos) (Real.Gamma_pos_of_pos (by linarith)))).ne')]
    simp only [Complex.cpow_one]
    ring
  let Gshift := Complex.Gamma (-t - q) / Complex.Gamma (t + q) *
    (Complex.Gamma (-p - 1) / Complex.Gamma (p + 1))
  let Gold := Complex.Gamma (-t) / Complex.Gamma t *
    (Complex.Gamma (-p) / Complex.Gamma p)
  have hscaled : (B * Gshift) * (lFun (-q) * lFun (1 - t) * lFun (1 + t + q)) =
      -C * Gold := by
    calc
      _ = (B * lFun (-q)) * (Gshift * (lFun (1 - t) * lFun (1 + t + q))) := by ring
      _ = (B * lFun (-q)) * (q ^ 2 * Gold) := by
        rw [(show Gshift * (lFun (1 - t) * lFun (1 + t + q)) = q ^ 2 * Gold by simpa [Gshift, Gold] using (gamma_ratio_shift_b (by dsimp [t, p, A, b, c, q]; field_simp [hγc]; ring) hΓt (show Complex.Gamma (-t) ≠ 0 by simpa [t, A] using hNegT) (show Complex.Gamma (t + q) ≠ 0 by simpa [t, A] using hTq) hΓnegTq (show Complex.Gamma p ≠ 0 by simpa [p, A] using hP) (show Complex.Gamma (p + 1) ≠ 0 by simpa [p, A] using hP1) (show Complex.Gamma (-p - 1) ≠ 0 by simpa [p, A, sub_eq_add_neg, add_comm] using hNegP1)))]
      _ = (B * q ^ 2) * lFun (-q) * Gold := by ring
      _ = _ := by rw [hcoeff]; field_simp [hLneg]
  have hfinal :
      reflectionDOZZ γ μ (α - γ / 2) =
        -C * reflectionDOZZ γ μ α /
          (lFun (-q) * lFun (1 - t) * lFun (1 + t + q)) := by
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero hLneg (by unfold lFun; rw [(show 1 - (1 - t) = t by ring)]; exact div_ne_zero (by simpa [t, A, sub_eq_add_neg, add_comm] using hOneSubT) hΓt)) (by unfold lFun; rw [(show 1 - (1 + t + q) = -t - q by ring)]; exact div_ne_zero (by simpa [t, A, add_assoc, add_comm, add_left_comm] using hOnePlusTq) hΓnegTq))).2
    rw [(show reflectionDOZZ γ μ (α - γ / 2) = -B ^ (p + 1) * Gshift by simp only [reflectionDOZZ, (show 2 * ((Q γ : ℂ) - (α - (γ : ℂ) / 2)) / (γ : ℂ) = p + 1 by simpa [Qc, b] using (by rw [hAshift]; dsimp [p, c, b]; field_simp [hγc])), (show (γ : ℂ) * ((Q γ : ℂ) - (α - (γ : ℂ) / 2)) / 2 = t + q by simpa [Qc, b] using (by rw [hAshift]; dsimp [t, b, q]; ring)), (show -(t + q) = -t - q by ring), (show -(p + 1) = -p - 1 by ring), Gshift, B]; ring), (show reflectionDOZZ γ μ α = -B ^ p * Gold by simp only [reflectionDOZZ, (show 2 * ((Q γ : ℂ) - α) / (γ : ℂ) = p by simpa [A, Qc] using (show 2 * A / (γ : ℂ) = p by dsimp [p, c]; field_simp [hγc])), (show (γ : ℂ) * ((Q γ : ℂ) - α) / 2 = t by simpa [A, Qc] using (by dsimp [t, b]; ring)), Gold, B]; ring), hpow]
    calc
      -(B * B ^ p) * Gshift * (lFun (-q) * lFun (1 - t) * lFun (1 + t + q)) =
        -B ^ p * ((B * Gshift) * (lFun (-q) * lFun (1 - t) * lFun (1 + t + q))) := by ring
      _ = -B ^ p * (-C * Gold) := by rw [hscaled]
      _ = -C * (-B ^ p * Gold) := by ring
  simpa [q, C, (show (γ : ℂ) * α / 2 - q = 1 - t by rw [htFormula]; ring), (show 2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * α / 2 = 1 + t + q by rw [htFormula]; ring), Complex.ofReal_mul] using hfinal


theorem reflectionDOZZ_shift_binv (hγ : 0 < γ) (hγ2 : γ < 2)
    (hγk : ∀ k : ℕ, 4 / γ ^ 2 ≠ (k : ℝ)) {μ : ℝ} (hμ : 0 < μ) :
    ∀ᶠ α in codiscrete ℂ,
      reflectionDOZZ γ μ α =
        -(((dozzBase γ μ : ℝ) : ℂ) ^ ((4 / γ ^ 2 : ℝ) : ℂ) / lFun ((4 / γ ^ 2 : ℝ) : ℂ)) *
          reflectionDOZZ γ μ (α + 2 / γ) /
          (lFun (-((4 / γ ^ 2 : ℝ) : ℂ)) * lFun (2 * α / γ) * lFun (2 + (4 / γ ^ 2 : ℝ) - 2 * α / γ)) := by
  have gamma_ratio_shift_binv {t} {p} {N} (htN : t * N = p) (hΓt : Complex.Gamma t ≠ 0) (hΓnegT : Complex.Gamma (-t) ≠ 0) (hΓtm1 : Complex.Gamma (t - 1) ≠ 0) (hΓp : Complex.Gamma p ≠ 0) (hΓnegP : Complex.Gamma (-p) ≠ 0) (hΓpmN : Complex.Gamma (p - N) ≠ 0) (hΓNmp : Complex.Gamma (N - p) ≠ 0) : (Complex.Gamma (-t) / Complex.Gamma t * (Complex.Gamma (-p) / Complex.Gamma p)) * (lFun (1 + N - p) * lFun (1 + p)) = N ^ 2 * (Complex.Gamma (1 - t) / Complex.Gamma (t - 1) * (Complex.Gamma (N - p) / Complex.Gamma (p - N))) := by
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
    have hrecT : Complex.Gamma t = (t - 1) * Complex.Gamma (t - 1) := by
      calc
        Complex.Gamma t = Complex.Gamma (t - 1 + 1) := congrArg Complex.Gamma (show t - 1 + 1 = t by ring).symm
        _ = (t - 1) * Complex.Gamma (t - 1) := Complex.Gamma_add_one (t - 1) htm1
    rw [(show 1 + N - p = 1 + (N - p) by ring), lFun_one_add hNmp, lFun_one_add hp, (show Complex.Gamma (1 - t) = -t * Complex.Gamma (-t) by simpa [sub_eq_add_neg, add_comm] using Complex.Gamma_add_one (-t) (neg_ne_zero.mpr ht)), hrecT]
    have halg : p * (N - p) = N ^ 2 * (-t) * (t - 1) := by
      calc
        p * (N - p) = (t * N) * (N - t * N) := by rw [htN]
        _ = N ^ 2 * (-t) * (t - 1) := by ring
    field_simp [hΓt, hΓnegT, hΓtm1, hΓp, hΓnegP, hΓpmN, hΓNmp,
      ht, htm1, hp, hNmp]
    rw [halg]
    ring_nf
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have : γ ^ 2 / 4 < 1 := by linarith only [pow_lt_pow_left₀ hγ2 hγ.le two_ne_zero]
  let B : ℂ := (dozzBase γ μ : ℝ)
  let NR : ℝ := 4 / γ ^ 2
  let N : ℂ := (NR : ℂ)
  have hNRpos : 0 < NR := by dsimp [NR]; positivity
  have hNne : N ≠ 0 := by
    dsimp [N]
    exact_mod_cast hNRpos.ne'
  have hNcast : ((4 / γ ^ 2 : ℝ) : ℂ) = N := rfl
  have hNcomplex : N = 4 / (γ : ℂ) ^ 2 := by
    dsimp [N, NR]
    push_cast
    field_simp [hγc]
  have hΓN : Complex.Gamma N ≠ 0 := by
    dsimp [N]
    rw [Complex.Gamma_ofReal]
    exact_mod_cast (Real.Gamma_pos_of_pos hNRpos).ne'
  have hΓnegN : Complex.Gamma (-N) ≠ 0 := by
    dsimp [N]
    apply Complex.Gamma_ne_zero
    intro k hk
    have hval : NR = (k : ℝ) := by
      have : -NR = -(k : ℝ) := by exact_mod_cast hk
      linarith
    exact hγk k (by simpa [NR] using hval)
  have hΓ1subN : Complex.Gamma (1 - N) ≠ 0 := by
    dsimp [N]
    apply Complex.Gamma_ne_zero
    intro k hk
    have hval : NR = (k + 1 : ℝ) := by
      have : 1 - NR = -(k : ℝ) := by exact_mod_cast hk
      linarith
    exact hγk (k + 1) (by simpa [NR] using hval)
  have hLN : lFun N ≠ 0 := by
    unfold lFun
    exact div_ne_zero hΓN hΓ1subN
  have hLnegN : lFun (-N) ≠ 0 := by
    unfold lFun
    apply div_ne_zero hΓnegN
    rw [show 1 - -N = 1 + N by ring]
    exact (by apply Complex.Gamma_ne_zero_of_re_pos; rw [add_re, one_re]; dsimp [N]; linarith)
  have hb : (γ : ℂ) / 2 ≠ 0 := div_ne_zero hγc (by norm_num)
  have hc : (2 : ℂ) / (γ : ℂ) ≠ 0 := div_ne_zero (by norm_num) hγc
  let b := (γ : ℂ) / 2
  let c := (2 : ℂ) / (γ : ℂ)
  let Qc := (Q γ : ℂ)
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
  let A := Qc - α
  let t : ℂ := b * A
  let p : ℂ := c * A
  have hΓnegP : Complex.Gamma (-p) ≠ 0 := by simpa [p, A] using hNegP
  have hΓpmN : Complex.Gamma (p - N) ≠ 0 := by
    simpa [p, A, sub_eq_add_neg, add_comm] using hPmN
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
    rw [hAshift]
    calc
      (γ : ℂ) * (A - c) / 2 = (γ : ℂ) * A / 2 - (γ : ℂ) * c / 2 := by ring
      _ = t - 1 := by
        rw [hTarg]
        rw [(show (γ : ℂ) * c / 2 = 1 by dsimp [c]; field_simp [hγc])]
  have hpFormula : p = 1 + N - 2 * α / (γ : ℂ) := by
    dsimp [p, c, A, Qc]
    rw [(show (Q γ : ℂ) = 2 / (γ : ℂ) + (γ : ℂ) / 2 by simp [Q]), hNcomplex]
    field_simp [hγc]
    ring
  have hLarg1 : 2 * α / (γ : ℂ) = 1 + N - p := by rw [hpFormula]; ring
  have hpow : B ^ p = B ^ N * B ^ (p - N) := by
    calc
      B ^ p = B ^ (N + (p - N)) := by congr 1; ring
      _ = B ^ N * B ^ (p - N) := Complex.cpow_add N (p - N) (by dsimp [B]; exact_mod_cast (show 0 < dozzBase γ μ by rw [dozzBase]; exact mul_pos (mul_pos Real.pi_pos hμ) (show 0 < (lFun ((γ : ℂ) ^ 2 / 4)).re by rw [(lFun_gammaSq_real γ), Complex.ofReal_re]; exact div_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.Gamma_pos_of_pos (by linarith)))).ne')
  let Gorig := Complex.Gamma (-t) / Complex.Gamma t *
    (Complex.Gamma (-p) / Complex.Gamma p)
  let Gshift := Complex.Gamma (1 - t) / Complex.Gamma (t - 1) *
    (Complex.Gamma (N - p) / Complex.Gamma (p - N))
  have hscaled : Gorig * (lFun N * lFun (-N) *
      lFun (1 + N - p) * lFun (1 + p)) = -Gshift := by
    calc
      _ = (Gorig * (lFun (1 + N - p) * lFun (1 + p))) *
          (lFun N * lFun (-N)) := by ring
      _ = (N ^ 2 * Gshift) * (lFun N * lFun (-N)) := by rw [(show Gorig * (lFun (1 + N - p) * lFun (1 + p)) = N ^ 2 * Gshift by simpa [Gorig, Gshift] using (gamma_ratio_shift_binv (by dsimp [t, p, A, b, c]; rw [hNcomplex]; field_simp [hγc]; ring) (by simpa [t, A] using hT) (show Complex.Gamma (-t) ≠ 0 by simpa [t, A] using hNegT) (show Complex.Gamma (t - 1) ≠ 0 by simpa [t, A, sub_eq_add_neg, add_comm] using hTm1) (show Complex.Gamma p ≠ 0 by simpa [p, A] using hP) hΓnegP hΓpmN (show Complex.Gamma (N - p) ≠ 0 by simpa [p, A, sub_eq_add_neg, add_comm] using hNmp)))]
      _ = -Gshift := by rw [(lFun_mul_neg hNne hΓN hΓnegN)]; field_simp [hNne]
  have hGammaCoeff :
      -Gorig * (lFun (-N) * lFun (1 + N - p) * lFun (1 + p)) = Gshift / lFun N := by
    apply (eq_div_iff hLN).2
    calc
      (-Gorig * (lFun (-N) * lFun (1 + N - p) * lFun (1 + p))) * lFun N =
          -(Gorig * (lFun N * lFun (-N) * lFun (1 + N - p) * lFun (1 + p))) := by ring
      _ = Gshift := by rw [hscaled]; ring
  have hfinal :
      reflectionDOZZ γ μ α =
        -(B ^ N / lFun N) * reflectionDOZZ γ μ (α + 2 / γ) /
          (lFun (-N) * lFun (1 + N - p) * lFun (1 + p)) := by
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero hLnegN (by unfold lFun; rw [(show 1 - (1 + N - p) = p - N by ring)]; exact div_ne_zero (by simpa [p, A, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hOnePlusNmp) hΓpmN)) (by unfold lFun; rw [(show 1 - (1 + p) = -p by ring)]; exact div_ne_zero (by simpa [p, A, add_comm] using hOnePlusP) hΓnegP))).2
    rw [(show reflectionDOZZ γ μ α = -B ^ p * Gorig by simp only [reflectionDOZZ, (show 2 * ((Q γ : ℂ) - α) / (γ : ℂ) = p by simpa [A, Qc] using hExp), (show (γ : ℂ) * ((Q γ : ℂ) - α) / 2 = t by simpa [A, Qc] using hTarg), Gorig, B]; ring), (show reflectionDOZZ γ μ (α + 2 / γ) = -B ^ (p - N) * Gshift by simp only [reflectionDOZZ, (show 2 * ((Q γ : ℂ) - (α + (2 : ℂ) / (γ : ℂ))) / (γ : ℂ) = p - N by simpa [Qc, c] using hExpShift), (show (γ : ℂ) * ((Q γ : ℂ) - (α + (2 : ℂ) / (γ : ℂ))) / 2 = t - 1 by simpa [Qc, c] using hTargShift), (show -(t - 1) = 1 - t by ring), (show -(p - N) = N - p by ring), Gshift, B]; ring)]
    calc
      (-B ^ p * Gorig) * (lFun (-N) * lFun (1 + N - p) * lFun (1 + p)) =
          B ^ p * (-Gorig * (lFun (-N) * lFun (1 + N - p) * lFun (1 + p))) := by ring
      _ = B ^ p * (Gshift / lFun N) := by rw [hGammaCoeff]
      _ = -(B ^ N / lFun N) * (-B ^ (p - N) * Gshift) := by
        rw [hpow]
        field_simp [hLN]
  have hLarg2' : 2 + N - (1 + N - p) = 1 + p := by ring
  simpa [N, hNcast, hLarg1, hLarg2', B, Complex.ofReal_mul] using hfinal

end DOZZ.Proofs
