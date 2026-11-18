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

private lemma ev_Gamma {f : ℂ → ℂ} {a : ℂ} (ha : a ≠ 0) (hf : ∀ α, f α = a * α + f 0) :
    ∀ᶠ α : ℂ in codiscrete ℂ, Complex.Gamma (f α) ≠ 0 ∧ f α ≠ 0 := by
  have hemb : IsClosedEmbedding fun n : ℕ => (-n - f 0) / a :=
    Metric.isClosedEmbedding_of_pairwise_le_dist (div_pos one_pos (norm_pos_iff.2 ha)) fun m n hmn => by
      dsimp only
      rw [dist_eq_norm, show (-m - f 0) / a - (-n - f 0) / a = (((n : ℝ) - m : ℝ) : ℂ) / a by
        push_cast; field_simp [ha]; ring, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact div_le_div_of_nonneg_right (Nat.pairwise_one_le_dist hmn) (norm_nonneg a)
  filter_upwards [compl_mem_codiscrete_iff.2 ⟨hemb.isClosed_range,
    hemb.isEmbedding.isInducing.isDiscrete_range⟩] with α hα
  have hΓ : Complex.Gamma (f α) ≠ 0 := Complex.Gamma_ne_zero fun n hn => hα ⟨n, by
    rw [hf] at hn; dsimp only; field_simp [ha]; linear_combination -hn⟩
  exact ⟨hΓ, fun h0 => hΓ (by simp [h0])⟩

private lemma lFun_one_add {z : ℂ} (hz : z ≠ 0) :
    lFun (1 + z) = z * (Complex.Gamma z / Complex.Gamma (-z)) := by
  unfold lFun
  rw [show 1 + z = z + 1 by ring, Complex.Gamma_add_one z hz, show 1 - (z + 1) = -z by ring]; ring

private lemma lFun_mul_neg {q : ℂ} (hq : q ≠ 0)
    (hΓq : Complex.Gamma q ≠ 0) (hΓnegq : Complex.Gamma (-q) ≠ 0) :
    lFun q * lFun (-q) = -1 / q ^ 2 := by
  unfold lFun
  rw [show 1 - q = -q + 1 by ring, Complex.Gamma_add_one (-q) (neg_ne_zero.2 hq),
    show 1 - -q = q + 1 by ring, Complex.Gamma_add_one q hq]
  field_simp [hq, hΓq, hΓnegq]

private lemma lFun_gammaSq_real (γ : ℝ) :
    lFun ((γ : ℂ) ^ 2 / 4) = ((Real.Gamma (γ ^ 2 / 4) / Real.Gamma (1 - γ ^ 2 / 4) : ℝ) : ℂ) := by
  rw [show ((γ : ℂ) ^ 2 / 4) = ((γ ^ 2 / 4 : ℝ) : ℂ) by push_cast; ring]
  unfold lFun
  rw [Complex.Gamma_ofReal, show (1 : ℂ) - ((γ ^ 2 / 4 : ℝ) : ℂ) = ((1 - γ ^ 2 / 4 : ℝ) : ℂ) by
    push_cast; ring, Complex.Gamma_ofReal, Complex.ofReal_div]

variable {γ : ℝ}

section
variable (hγ : 0 < γ) (hγ2 : γ < 2)
include hγ hγ2

private lemma dozzBase_ne_zero_c {μ : ℝ} (hμ : 0 < μ) : ((dozzBase γ μ : ℝ) : ℂ) ≠ 0 := by
  refine Complex.ofReal_ne_zero.2 (mul_pos (mul_pos Real.pi_pos hμ) ?_).ne'
  rw [lFun_gammaSq_real γ, Complex.ofReal_re]
  exact div_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.Gamma_pos_of_pos (by nlinarith))

/-- First reflection shift [KRV, (shift1DOZZ)] (correct as printed). -/
theorem reflectionDOZZ_shift_b {μ : ℝ} (hμ : 0 < μ) :
    ∀ᶠ α in codiscrete ℂ,
      reflectionDOZZ γ μ (α - γ / 2) =
        -(μ * Real.pi) * reflectionDOZZ γ μ α /
          (lFun (-(γ ^ 2 / 4)) * lFun (γ * α / 2 - γ ^ 2 / 4) * lFun (2 + γ ^ 2 / 2 - γ * α / 2)) := by
  have hγc := Complex.ofReal_ne_zero.2 hγ.ne'
  have hqRpos : 0 < γ ^ 2 / 4 := by positivity
  have hqRlt : γ ^ 2 / 4 < 1 := by nlinarith
  let q := (γ : ℂ) ^ 2 / 4
  have hqCast : ((γ ^ 2 / 4 : ℝ) : ℂ) = q := by dsimp [q]; push_cast; ring
  have hqne : q ≠ 0 := div_ne_zero (pow_ne_zero 2 hγc) (by norm_num)
  have hΓq : Complex.Gamma q ≠ 0 := by
    rw [← hqCast, Complex.Gamma_ofReal]; exact_mod_cast (Real.Gamma_pos_of_pos hqRpos).ne'
  have hΓnegq : Complex.Gamma (-q) ≠ 0 := Complex.Gamma_ne_zero fun n hn => by
    have hq' : γ ^ 2 / 4 = (n : ℝ) := neg_inj.1 (by exact_mod_cast (by rwa [← hqCast] at hn : -((γ ^ 2 / 4 : ℝ) : ℂ) = -(n : ℂ)))
    rcases Nat.eq_zero_or_pos n with rfl | hnp <;>
      [linarith [show (0 : ℝ) = ((0 : ℕ) : ℝ) by norm_num]; linarith [show (1 : ℝ) ≤ n from mod_cast hnp]]
  have hLneg : lFun (-q) ≠ 0 := div_ne_zero hΓnegq (by
    rw [show 1 - -q = 1 + q by ring]
    exact Complex.Gamma_ne_zero_of_re_pos (by rw [add_re, one_re, ← hqCast, Complex.ofReal_re]; linarith))
  let B : ℂ := (dozzBase γ μ : ℝ)
  let C : ℂ := (μ * Real.pi : ℝ)
  have hBne : B ≠ 0 := dozzBase_ne_zero_c hγ hγ2 hμ
  have hcoeff : B * q ^ 2 = -C / lFun (-q) := (eq_div_iff hLneg).2 (by
    have hbEq : B = C * lFun q := by
      dsimp [B, C, dozzBase]; rw [lFun_gammaSq_real γ, Complex.ofReal_re]; push_cast; ring
    rw [hbEq, show C * lFun q * q ^ 2 * lFun (-q) = C * (lFun q * lFun (-q)) * q ^ 2 by ring,
      lFun_mul_neg hqne hΓq hΓnegq]
    field_simp [hqne])
  let b := (γ : ℂ) / 2; let c := 2 / (γ : ℂ); let Qc : ℂ := (Q γ : ℂ)
  have hb : b ≠ 0 := div_ne_zero hγc (by norm_num)
  have hc : c ≠ 0 := div_ne_zero (by norm_num) hγc
  filter_upwards [
    ev_Gamma (f := fun α => b * (Qc - α)) (neg_ne_zero.2 hb) (fun _ => by ring),
    ev_Gamma (f := fun α => -(b * (Qc - α))) hb (fun _ => by ring),
    ev_Gamma (f := fun α => b * (Qc - α) + q) (neg_ne_zero.2 hb) (fun _ => by ring),
    ev_Gamma (f := fun α => -(b * (Qc - α)) - q) hb (fun _ => by ring),
    ev_Gamma (f := fun α => c * (Qc - α)) (neg_ne_zero.2 hc) (fun _ => by ring),
    ev_Gamma (f := fun α => c * (Qc - α) + 1) (neg_ne_zero.2 hc) (fun _ => by ring),
    ev_Gamma (f := fun α => -(c * (Qc - α)) - 1) hc (fun _ => by ring),
    ev_Gamma (f := fun α => 1 - b * (Qc - α)) hb (fun _ => by ring),
    ev_Gamma (f := fun α => 1 + b * (Qc - α) + q) (neg_ne_zero.2 hb) (fun _ => by ring)]
    with α ⟨hΓt, ht⟩ ⟨hΓnegT, _⟩ ⟨hΓtq, htq'⟩ ⟨hΓnegTq, _⟩ ⟨hΓp, hp⟩ ⟨hΓp1, hp1⟩
      ⟨hΓnegP1, hnp1⟩ ⟨hΓ1subT, _⟩ ⟨hΓ1plusTq, _⟩
  set t : ℂ := b * (Qc - α)
  set p : ℂ := c * (Qc - α)
  have htq : t = q * p := by dsimp [t, p, b, c, q]; field_simp [hγc]; ring
  have hL1 : lFun (1 - t) ≠ 0 := by unfold lFun; rw [show 1 - (1 - t) = t by ring]; exact div_ne_zero hΓ1subT hΓt
  have hL2 : lFun (1 + t + q) ≠ 0 := by unfold lFun; rw [show 1 - (1 + t + q) = -t - q by ring]; exact div_ne_zero hΓ1plusTq hΓnegTq
  have hratio : (Complex.Gamma (-t - q) / Complex.Gamma (t + q) * (Complex.Gamma (-p - 1) / Complex.Gamma (p + 1))) *
      (lFun (1 - t) * lFun (1 + t + q)) =
      q ^ 2 * (Complex.Gamma (-t) / Complex.Gamma t * (Complex.Gamma (-p) / Complex.Gamma p)) := by
    have hlsub : lFun (1 - t) = -t * (Complex.Gamma (-t) / Complex.Gamma t) := by
      unfold lFun; rw [show 1 - t = -t + 1 by ring, Complex.Gamma_add_one (-t) (neg_ne_zero.2 ht),
        show 1 - (-t + 1) = t by ring]; ring
    have hrecN : Complex.Gamma (-p) = (-p - 1) * Complex.Gamma (-p - 1) := by
      conv_lhs => rw [show -p = (-p - 1) + 1 by ring]
      exact Complex.Gamma_add_one (-p - 1) hnp1
    rw [hlsub, show 1 + t + q = 1 + (t + q) by ring, lFun_one_add htq', hrecN, Complex.Gamma_add_one p hp,
      show -(t + q) = -t - q by ring]
    field_simp [hΓt, hΓnegT, hΓtq, hΓnegTq, hΓp, hΓnegP1, ht, htq', hp, hp1]
    rw [htq]; ring
  have ht_val : t = 1 + q - (γ : ℂ) * α / 2 := by
    dsimp [t, b, Qc, q]; rw [show (Q γ : ℂ) = 2 / (γ : ℂ) + (γ : ℂ) / 2 by simp [Q]]; field_simp [hγc]; ring
  have hExpS : 2 * ((Q γ : ℂ) - (α - (γ : ℂ) / 2)) / (γ : ℂ) = p + 1 := by dsimp [p, c, Qc]; field_simp [hγc]; ring
  have hTargS : (γ : ℂ) * ((Q γ : ℂ) - (α - (γ : ℂ) / 2)) / 2 = t + q := by dsimp [t, b, Qc, q]; ring
  let Gshift : ℂ := Complex.Gamma (-t - q) / Complex.Gamma (t + q) * (Complex.Gamma (-p - 1) / Complex.Gamma (p + 1))
  let Gold : ℂ := Complex.Gamma (-t) / Complex.Gamma t * (Complex.Gamma (-p) / Complex.Gamma p)
  rw [show (γ : ℂ) * α / 2 - q = 1 - t by linear_combination ht_val,
    show 2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * α / 2 = 1 + t + q by dsimp [q] at ht_val; linear_combination -ht_val,
    show reflectionDOZZ γ μ (α - γ / 2) = -(B * B ^ p) * Gshift by
      simp only [reflectionDOZZ, hExpS, hTargS, show -(t + q) = -t - q by ring, show -(p + 1) = -p - 1 by ring, Gshift, B]
      rw [Complex.cpow_add p 1 hBne, Complex.cpow_one]; ring,
    show reflectionDOZZ γ μ α = -B ^ p * Gold by
      simp only [reflectionDOZZ, show 2 * ((Q γ : ℂ) - α) / (γ : ℂ) = p by dsimp [p, c, Qc]; ring,
        show (γ : ℂ) * ((Q γ : ℂ) - α) / 2 = t by dsimp [t, b, Qc]; ring, Gold, B]; ring,
    show -(μ * Real.pi : ℂ) = -C by dsimp [C]; push_cast; rfl]
  refine (eq_div_iff (mul_ne_zero (mul_ne_zero hLneg hL1) hL2)).2 ?_
  calc -(B * B ^ p) * Gshift * (lFun (-q) * lFun (1 - t) * lFun (1 + t + q))
    _ = -B ^ p * (B * lFun (-q) * (Gshift * (lFun (1 - t) * lFun (1 + t + q)))) := by ring
    _ = -B ^ p * ((B * q ^ 2) * lFun (-q) * Gold) := by rw [hratio]; ring
    _ = -C * (-B ^ p * Gold) := by rw [hcoeff]; field_simp [hLneg]

theorem reflectionDOZZ_shift_binv
    (hγk : ∀ k : ℕ, 4 / γ ^ 2 ≠ (k : ℝ)) {μ : ℝ} (hμ : 0 < μ) :
    ∀ᶠ α in codiscrete ℂ,
      reflectionDOZZ γ μ α =
        -(((dozzBase γ μ : ℝ) : ℂ) ^ ((4 / γ ^ 2 : ℝ) : ℂ) / lFun ((4 / γ ^ 2 : ℝ) : ℂ)) *
          reflectionDOZZ γ μ (α + 2 / γ) /
          (lFun (-((4 / γ ^ 2 : ℝ) : ℂ)) * lFun (2 * α / γ) * lFun (2 + (4 / γ ^ 2 : ℝ) - 2 * α / γ)) := by
  have hγc := Complex.ofReal_ne_zero.2 hγ.ne'
  let B : ℂ := (dozzBase γ μ : ℝ)
  have hBne : B ≠ 0 := dozzBase_ne_zero_c hγ hγ2 hμ
  let N : ℂ := ((4 / γ ^ 2 : ℝ) : ℂ)
  have hNRpos : 0 < 4 / γ ^ 2 := by positivity
  have hNne : N ≠ 0 := Complex.ofReal_ne_zero.2 hNRpos.ne'
  have hNval : N = 4 / (γ : ℂ) ^ 2 := by dsimp [N]; push_cast; ring
  have hΓN : Complex.Gamma N ≠ 0 := by
    dsimp [N]; rw [Complex.Gamma_ofReal]; exact_mod_cast (Real.Gamma_pos_of_pos hNRpos).ne'
  have hΓnegN : Complex.Gamma (-N) ≠ 0 := Complex.Gamma_ne_zero fun k hk => by
    dsimp [N] at hk; exact hγk k (neg_inj.1 (by exact_mod_cast hk))
  have hLN : lFun N ≠ 0 := div_ne_zero hΓN (Complex.Gamma_ne_zero fun k hk => by
    dsimp [N] at hk
    exact hγk (k + 1) (by push_cast; linarith [show 1 - 4 / γ ^ 2 = -(k : ℝ) by exact_mod_cast hk]))
  have hLnegN : lFun (-N) ≠ 0 := div_ne_zero hΓnegN (by
    rw [show 1 - -N = 1 + N by ring]
    exact Complex.Gamma_ne_zero_of_re_pos (by rw [add_re, one_re]; dsimp [N]; linarith))
  let b : ℂ := (γ : ℂ) / 2; let c : ℂ := 2 / (γ : ℂ); let Qc : ℂ := (Q γ : ℂ)
  have hb : b ≠ 0 := div_ne_zero hγc (by norm_num)
  have hc : c ≠ 0 := div_ne_zero (by norm_num) hγc
  filter_upwards [
    ev_Gamma (f := fun α => b * (Qc - α)) (neg_ne_zero.2 hb) (fun _ => by ring),
    ev_Gamma (f := fun α => -(b * (Qc - α))) hb (fun _ => by ring),
    ev_Gamma (f := fun α => b * (Qc - α) - 1) (neg_ne_zero.2 hb) (fun _ => by ring),
    ev_Gamma (f := fun α => c * (Qc - α)) (neg_ne_zero.2 hc) (fun _ => by ring),
    ev_Gamma (f := fun α => -(c * (Qc - α))) hc (fun _ => by ring),
    ev_Gamma (f := fun α => c * (Qc - α) - N) (neg_ne_zero.2 hc) (fun _ => by ring),
    ev_Gamma (f := fun α => N - c * (Qc - α)) hc (fun _ => by ring),
    ev_Gamma (f := fun α => 1 + N - c * (Qc - α)) hc (fun _ => by ring),
    ev_Gamma (f := fun α => 1 + c * (Qc - α)) (neg_ne_zero.2 hc) (fun _ => by ring)]
    with α ⟨hΓt, ht⟩ ⟨hΓnegT, _⟩ ⟨hΓtm1, htm1⟩ ⟨hΓp, hp⟩ ⟨hΓnegP, _⟩
      ⟨hΓpmN, _⟩ ⟨hΓNmp, hNmp_ne⟩ ⟨hΓ1plusNmp, _⟩ ⟨hΓ1plusP, _⟩
  set t : ℂ := b * (Qc - α)
  set p : ℂ := c * (Qc - α)
  have htN : t * N = p := by dsimp [t, p, b, c]; rw [hNval]; field_simp [hγc]; ring
  have hL1 : lFun (1 + N - p) ≠ 0 := by unfold lFun; rw [show 1 - (1 + N - p) = p - N by ring]; exact div_ne_zero hΓ1plusNmp hΓpmN
  have hL2 : lFun (1 + p) ≠ 0 := by unfold lFun; rw [show 1 - (1 + p) = -p by ring]; exact div_ne_zero hΓ1plusP hΓnegP
  have hratio : (Complex.Gamma (-t) / Complex.Gamma t * (Complex.Gamma (-p) / Complex.Gamma p)) *
      (lFun (1 + N - p) * lFun (1 + p)) =
      N ^ 2 * (Complex.Gamma (1 - t) / Complex.Gamma (t - 1) * (Complex.Gamma (N - p) / Complex.Gamma (p - N))) := by
    have hrecTm : Complex.Gamma (1 - t) = -t * Complex.Gamma (-t) := by
      simpa [sub_eq_add_neg, add_comm] using Complex.Gamma_add_one (-t) (neg_ne_zero.2 ht)
    have hrecT : Complex.Gamma t = (t - 1) * Complex.Gamma (t - 1) := by
      conv_lhs => rw [show t = (t - 1) + 1 by ring]
      exact Complex.Gamma_add_one (t - 1) htm1
    rw [show 1 + N - p = 1 + (N - p) by ring, lFun_one_add hNmp_ne, lFun_one_add hp, hrecTm, hrecT,
      show -(N - p) = p - N by ring]
    field_simp [hΓt, hΓnegT, hΓtm1, hΓp, hΓnegP, hΓpmN, hΓNmp, ht, htm1, hp, hNmp_ne]
    rw [← htN]; ring
  have hp_val : p = 1 + N - 2 * α / (γ : ℂ) := by
    dsimp [p, c, Qc]; rw [show (Q γ : ℂ) = 2 / (γ : ℂ) + (γ : ℂ) / 2 by simp [Q], hNval]; field_simp [hγc]; ring
  have hExpS : 2 * ((Q γ : ℂ) - (α + 2 / (γ : ℂ))) / (γ : ℂ) = p - N := by
    dsimp [p, c, Qc]; rw [hNval]; field_simp [hγc]; ring
  have hTargS : (γ : ℂ) * ((Q γ : ℂ) - (α + 2 / (γ : ℂ))) / 2 = t - 1 := by
    dsimp [t, b, Qc]; field_simp [hγc]; ring
  let Gorig : ℂ := Complex.Gamma (-t) / Complex.Gamma t * (Complex.Gamma (-p) / Complex.Gamma p)
  let Gshift : ℂ := Complex.Gamma (1 - t) / Complex.Gamma (t - 1) * (Complex.Gamma (N - p) / Complex.Gamma (p - N))
  change reflectionDOZZ γ μ α = -(B ^ N / lFun N) * reflectionDOZZ γ μ (α + 2 / γ) /
    (lFun (-N) * lFun (2 * α / γ) * lFun (2 + N - 2 * α / γ))
  rw [show 2 + N - 2 * α / (γ : ℂ) = 1 + p by linear_combination -hp_val,
    show 2 * α / (γ : ℂ) = 1 + N - p by linear_combination hp_val,
    show reflectionDOZZ γ μ α = -(B ^ N * B ^ (p - N)) * Gorig by
      simp only [reflectionDOZZ, show 2 * ((Q γ : ℂ) - α) / (γ : ℂ) = p by dsimp [p, c, Qc]; ring,
        show (γ : ℂ) * ((Q γ : ℂ) - α) / 2 = t by dsimp [t, b, Qc]; ring, Gorig, B]
      rw [← Complex.cpow_add N (p - N) hBne, show N + (p - N) = p by ring]; ring,
    show reflectionDOZZ γ μ (α + 2 / γ) = -B ^ (p - N) * Gshift by
      simp only [reflectionDOZZ, hExpS, hTargS, show -(t - 1) = 1 - t by ring, show -(p - N) = N - p by ring, Gshift, B]; ring]
  refine (eq_div_iff (mul_ne_zero (mul_ne_zero hLnegN hL1) hL2)).2 ((mul_left_inj' hLN).1 ?_)
  have hscaled : Gorig * (lFun (-N) * lFun (1 + N - p) * lFun (1 + p)) * lFun N = -Gshift := by
    calc Gorig * (lFun (-N) * lFun (1 + N - p) * lFun (1 + p)) * lFun N
      _ = (Gorig * (lFun (1 + N - p) * lFun (1 + p))) * (lFun N * lFun (-N)) := by ring
      _ = Gshift * (N ^ 2 * (-1 / N ^ 2)) := by rw [hratio, lFun_mul_neg hNne hΓN hΓnegN]; ring
      _ = -Gshift := by field_simp [hNne]
  calc -(B ^ N * B ^ (p - N)) * Gorig * (lFun (-N) * lFun (1 + N - p) * lFun (1 + p)) * lFun N
    _ = -B ^ N * B ^ (p - N) * (Gorig * (lFun (-N) * lFun (1 + N - p) * lFun (1 + p)) * lFun N) := by ring
    _ = -(B ^ N / lFun N * lFun N) * B ^ (p - N) * (-Gshift) := by rw [hscaled, div_mul_cancel₀ _ hLN]
    _ = -(B ^ N / lFun N) * (-B ^ (p - N) * Gshift) * lFun N := by ring

end
end DOZZ.Proofs
