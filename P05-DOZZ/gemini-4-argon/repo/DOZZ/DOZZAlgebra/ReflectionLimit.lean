/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# DOZZ — punctured limit of the reflection coefficient at Q
-/

@[expose] public section

open Complex Filter Set Topology

namespace DOZZ.Proofs

variable {γ : ℝ}

/-- The reflection coefficient has punctured limit `-1` at `Q`. -/
theorem reflectionDOZZ_tendsto_Q (hγ : 0 < γ) (hγ2 : γ < 2) {μ} (hμ : 0 < μ) :
    Tendsto (reflectionDOZZ γ μ) (𝓝[≠] (Q γ : ℂ)) (𝓝 (-1)) := by
  have hγne : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'

  have : γ ^ 2 < 4 := by nlinarith [mul_pos (sub_pos.mpr hγ2) (by linarith : 0 < 2 + γ)]
  have : γ ^ 2 / 4 < 1 := by nlinarith
  have hlFun :
      lFun ((γ : ℂ) ^ 2 / 4) =
        ((Real.Gamma (γ ^ 2 / 4) / Real.Gamma (1 - γ ^ 2 / 4) : ℝ) : ℂ) := by
    rw [(show ((γ : ℂ) ^ 2 / 4) = ((γ ^ 2 / 4 : ℝ) : ℂ) by push_cast; ring)]
    unfold lFun
    rw [Complex.Gamma_ofReal, (show Complex.Gamma (1 - (γ ^ 2 / 4 : ℝ)) = (Real.Gamma (1 - γ ^ 2 / 4) : ℂ) by convert Complex.Gamma_ofReal (1 - γ ^ 2 / 4) using 1; simp)]
    exact (Complex.ofReal_div _ _).symm
  have hlpos : 0 < (lFun ((γ : ℂ) ^ 2 / 4)).re := by
    rw [hlFun]
    simp only [Complex.ofReal_re]
    exact div_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.Gamma_pos_of_pos (by linarith))
  let B : ℂ := (dozzBase γ μ : ℝ)
  let d : ℂ → ℂ := fun α => (Q γ : ℂ) - α
  let x₁ : ℂ → ℂ := fun α => (γ : ℂ) * d α / 2
  let x₂ : ℂ → ℂ := fun α => 2 * d α / (γ : ℂ)
  let e : ℂ → ℂ := fun α => 2 * d α / (γ : ℂ)

  have hd : Tendsto d (𝓝[≠] (Q γ : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcont : ContinuousAt d (Q γ : ℂ) := by
        dsimp [d]
        fun_prop
      simpa [d] using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with α hα
      simp only [mem_compl_iff, mem_singleton_iff] at hα
      change d α ≠ 0
      dsimp [d]
      exact sub_ne_zero.mpr (Ne.symm hα)

  have hscale : ∀ c : ℂ, c ≠ 0 →
      Tendsto (fun α => c * d α) (𝓝[≠] (Q γ : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    intro c hc
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hd₀ := tendsto_nhds_of_tendsto_nhdsWithin hd
      simpa using Tendsto.const_mul c hd₀
    · filter_upwards [self_mem_nhdsWithin] with α hα
      simp only [mem_compl_iff, mem_singleton_iff] at hα
      exact mul_ne_zero hc (by dsimp [d]; exact sub_ne_zero.mpr (Ne.symm hα))

  have hGammaRatio :
      Tendsto (fun x => Complex.Gamma (-x) / Complex.Gamma x)
        (𝓝[≠] (0 : ℂ)) (𝓝 (-1)) := by
    have hminus : Tendsto (fun x => Complex.Gamma (1 - x))
        (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
      simpa only [Complex.Gamma_one] using (show Tendsto (fun x => Complex.Gamma (1 - x))
        (𝓝[≠] (0 : ℂ)) (𝓝 (Complex.Gamma 1)) from by
          convert (Complex.continuousAt_Gamma_one.tendsto.comp (show Tendsto (fun x => 1 - x) (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) by simpa using (show ContinuousAt (fun x : ℂ => 1 - x) 0 by fun_prop).tendsto.mono_left nhdsWithin_le_nhds)) using 1
          ext x
          rfl)
    have hplus : Tendsto (fun x => Complex.Gamma (1 + x))
        (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
      simpa only [Complex.Gamma_one] using (show Tendsto (fun x => Complex.Gamma (1 + x))
        (𝓝[≠] (0 : ℂ)) (𝓝 (Complex.Gamma 1)) from by
          convert (Complex.continuousAt_Gamma_one.tendsto.comp (show Tendsto (fun x => 1 + x) (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) by simpa using (show ContinuousAt (fun x : ℂ => 1 + x) 0 by fun_prop).tendsto.mono_left nhdsWithin_le_nhds)) using 1
          ext x
          rfl)
    have hquot : Tendsto
        (fun x => Complex.Gamma (1 - x) / Complex.Gamma (1 + x))
        (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
      convert hminus.div hplus one_ne_zero using 1
      ext x
      simp
    have hlocal : ∀ᶠ x : ℂ in 𝓝[≠] (0 : ℂ),
        Complex.Gamma (-x) / Complex.Gamma x =
          -(Complex.Gamma (1 - x) / Complex.Gamma (1 + x)) := by
      filter_upwards [(show ∀ᶠ x : ℂ in 𝓝[≠] (0 : ℂ), ‖x‖ < 1 by filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ one_pos)] with x hx; simpa [Metric.mem_ball] using hx), self_mem_nhdsWithin] with x hxsmall hxmem
      have hx0 : x ≠ 0 := by simpa using hxmem
      have := (abs_lt.mp (lt_of_le_of_lt (Complex.abs_re_le_norm x) hxsmall)).1
      have hG : Complex.Gamma (1 + x) ≠ 0 := by
        apply Complex.Gamma_ne_zero_of_re_pos
        rw [add_re, one_re]
        linarith
      rw [(show Complex.Gamma (-x) = Complex.Gamma (1 - x) / (-x) by apply (eq_div_iff (neg_ne_zero.mpr hx0)).2; simpa [mul_comm] using (show Complex.Gamma (1 - x) = (-x) * Complex.Gamma (-x) by simpa [sub_eq_add_neg, add_comm] using Complex.Gamma_add_one (-x) (neg_ne_zero.mpr hx0)).symm), (show Complex.Gamma x = Complex.Gamma (1 + x) / x by apply (eq_div_iff hx0).2; simpa [mul_comm] using (show Complex.Gamma (1 + x) = x * Complex.Gamma x by simpa [add_comm] using Complex.Gamma_add_one x hx0).symm)]
      field_simp [hx0, hG]
    exact (tendsto_congr' hlocal).mpr (by simpa using hquot.neg)

  have hpow : Tendsto (fun α => B ^ e α)
      (𝓝[≠] (Q γ : ℂ)) (𝓝 (1 : ℂ)) := by
    have h := tendsto_const_nhds.cpow (by simpa [e] using (show Tendsto (fun α => (2 : ℂ) * d α) (𝓝[≠] (Q γ : ℂ)) (𝓝 (0 : ℂ)) by simpa using Tendsto.const_mul (2 : ℂ) (tendsto_nhds_of_tendsto_nhdsWithin hd)).div_const (γ : ℂ)) (show B ∈ Complex.slitPlane by dsimp [B]; exact Complex.ofReal_mem_slitPlane.2 (by rw [dozzBase]; exact mul_pos (mul_pos Real.pi_pos hμ) hlpos))
    simpa [B] using h

  rw [(show reflectionDOZZ γ μ = fun α => -(B ^ e α) * (Complex.Gamma (-x₁ α) / Complex.Gamma (x₁ α)) * (Complex.Gamma (-x₂ α) / Complex.Gamma (x₂ α)) by funext α; simp [reflectionDOZZ, B, e, d, x₁, x₂])]
  simpa using ((hpow.neg).mul (hGammaRatio.comp (by convert hscale ((γ : ℂ) / 2) (div_ne_zero hγne (by norm_num)) using 1; ext α; simp [x₁, d]; ring)) |>.mul (hGammaRatio.comp (by convert hscale ((2 : ℂ) / (γ : ℂ)) (div_ne_zero (by norm_num) hγne) using 1; ext α; simp [x₂, d]; ring)))

end DOZZ.Proofs
