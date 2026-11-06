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
theorem reflectionDOZZ_tendsto_Q (hγ : 0 < γ) (hγ2 : γ < 2) {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (reflectionDOZZ γ μ) (𝓝[≠] (Q γ : ℂ)) (𝓝 (-1)) := by
  have hγne : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'

  have hu₀ : 0 < γ ^ 2 / 4 := by positivity
  have hγlt : γ ^ 2 < 4 := by nlinarith
  have hu₁ : γ ^ 2 / 4 < 1 := by nlinarith

  have hgammaNum : 0 < Real.Gamma (γ ^ 2 / 4) :=
    Real.Gamma_pos_of_pos hu₀
  have hgammaDen : 0 < Real.Gamma (1 - γ ^ 2 / 4) :=
    by positivity
  have harg : ((γ : ℂ) ^ 2 / 4) = ((γ ^ 2 / 4 : ℝ) : ℂ) := by
    push_cast
    ring
  have hlFun :
      lFun ((γ : ℂ) ^ 2 / 4) =
        ((Real.Gamma (γ ^ 2 / 4) / Real.Gamma (1 - γ ^ 2 / 4) : ℝ) : ℂ) := by
    rw [harg]
    unfold lFun
    have hden : Complex.Gamma (1 - (γ ^ 2 / 4 : ℝ)) =
        (Real.Gamma (1 - γ ^ 2 / 4) : ℂ) := by
      convert Complex.Gamma_ofReal _ using 1
      simp
    rw [Complex.Gamma_ofReal, hden]
    simp
  have hlpos : 0 < (lFun ((γ : ℂ) ^ 2 / 4)).re := by
    simp_all
  have hbase : 0 < dozzBase γ μ := by
    rw [dozzBase]
    positivity

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
      grind

  have hscale : ∀ c : ℂ, c ≠ 0 →
      Tendsto (fun α => c * d α) (𝓝[≠] (Q γ : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    intro c hc
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hd₀ := tendsto_nhds_of_tendsto_nhdsWithin hd
      simpa using Tendsto.const_mul c hd₀
    · filter_upwards [self_mem_nhdsWithin] with α hα
      grind

  have hx₁ : Tendsto x₁ (𝓝[≠] (Q γ : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    have hc : ((γ : ℂ) / 2) ≠ 0 := by simp_all
    convert hscale ((γ : ℂ) / 2) hc using 1
    ext α
    simp [x₁, d]
    ring
  have hx₂ : Tendsto x₂ (𝓝[≠] (Q γ : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    have hc : (2 : ℂ) / (γ : ℂ) ≠ 0 := by simp_all
    convert hscale ((2 : ℂ) / (γ : ℂ)) hc using 1
    ext α
    simp [x₂, d]
    ring

  have hsmall : ∀ᶠ x : ℂ in 𝓝[≠] (0 : ℂ), ‖x‖ < 1 := by
    have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ one_pos
    filter_upwards [mem_nhdsWithin_of_mem_nhds hball] with x hx
    simpa [Metric.mem_ball] using hx

  have hGammaRatio :
      Tendsto (fun x : ℂ => Complex.Gamma (-x) / Complex.Gamma x)
        (𝓝[≠] (0 : ℂ)) (𝓝 (-1)) := by
    have hminus : Tendsto (fun x : ℂ => Complex.Gamma (1 - x))
        (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
      have harg : Tendsto (fun x : ℂ => 1 - x) (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
        have hcont : ContinuousAt (fun x : ℂ => 1 - x) 0 := by fun_prop
        simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
      simpa only [Complex.Gamma_one] using (show Tendsto (fun x : ℂ => Complex.Gamma (1 - x))
        (𝓝[≠] (0 : ℂ)) (𝓝 (Complex.Gamma 1)) from by
          convert (Complex.continuousAt_Gamma_one.tendsto.comp harg) using 1
          ext x
          rfl)
    have hplus : Tendsto (fun x : ℂ => Complex.Gamma (1 + x))
        (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
      have harg : Tendsto (fun x : ℂ => 1 + x) (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
        have hcont : ContinuousAt (fun x : ℂ => 1 + x) 0 := by fun_prop
        simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
      simpa only [Complex.Gamma_one] using (show Tendsto (fun x : ℂ => Complex.Gamma (1 + x))
        (𝓝[≠] (0 : ℂ)) (𝓝 (Complex.Gamma 1)) from by
          convert (Complex.continuousAt_Gamma_one.tendsto.comp harg) using 1
          ext x
          rfl)
    have hquot : Tendsto
        (fun x : ℂ => Complex.Gamma (1 - x) / Complex.Gamma (1 + x))
        (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
      convert hminus.div hplus one_ne_zero using 1
      ext x
      simp
    have hlocal : ∀ᶠ x : ℂ in 𝓝[≠] (0 : ℂ),
        Complex.Gamma (-x) / Complex.Gamma x =
          -(Complex.Gamma (1 - x) / Complex.Gamma (1 + x)) := by
      filter_upwards [hsmall, self_mem_nhdsWithin] with x hxsmall hxmem
      have hx0 : x ≠ 0 := by assumption
      have hxre : -1 < x.re := by
        have habs : |x.re| < 1 := lt_of_le_of_lt (Complex.abs_re_le_norm x) hxsmall
        exact (abs_lt.mp habs).1
      have hG : Complex.Gamma (1 + x) ≠ 0 := by
        apply Complex.Gamma_ne_zero_of_re_pos
        rw [add_re, one_re]
        linarith
      have hrecNeg : Complex.Gamma (1 - x) = (-x) * Complex.Gamma (-x) := by
        simpa [sub_eq_add_neg, add_comm] using
          Complex.Gamma_add_one (-x) (neg_ne_zero.mpr hx0)
      have hrecPos : Complex.Gamma (1 + x) = x * Complex.Gamma x := by
        simpa [add_comm] using Complex.Gamma_add_one x hx0
      have hneg : Complex.Gamma (-x) = Complex.Gamma (1 - x) / (-x) := by
        apply (eq_div_iff (neg_ne_zero.mpr hx0)).2
        simpa [mul_comm] using hrecNeg.symm
      have hpos : Complex.Gamma x = Complex.Gamma (1 + x) / x := by
        apply (eq_div_iff hx0).2
        simpa [mul_comm] using hrecPos.symm
      rw [hneg, hpos]
      field_simp [hx0, hG]
    have hquotNeg : Tendsto
        (fun x : ℂ => -(Complex.Gamma (1 - x) / Complex.Gamma (1 + x)))
        (𝓝[≠] (0 : ℂ)) (𝓝 (-1)) := by
      simpa using hquot.neg
    exact (tendsto_congr' hlocal).mpr hquotNeg

  have hR₁ : Tendsto (fun α => Complex.Gamma (-x₁ α) / Complex.Gamma (x₁ α))
      (𝓝[≠] (Q γ : ℂ)) _ := hGammaRatio.comp hx₁
  have hR₂ : Tendsto (fun α => Complex.Gamma (-x₂ α) / Complex.Gamma (x₂ α))
      (𝓝[≠] (Q γ : ℂ)) _ := hGammaRatio.comp hx₂

  have he : Tendsto e (𝓝[≠] (Q γ : ℂ)) (𝓝 (0 : ℂ)) := by
    have hmul : Tendsto (fun α => (2 : ℂ) * d α)
        (𝓝[≠] (Q γ : ℂ)) (𝓝 (0 : ℂ)) := by
      simpa using Tendsto.const_mul (2 : ℂ) (tendsto_nhds_of_tendsto_nhdsWithin hd)
    simpa [e] using hmul.div_const (γ : ℂ)
  have hpow : Tendsto (fun α => B ^ e α)
      (𝓝[≠] (Q γ : ℂ)) (𝓝 (1 : ℂ)) := by
    have hB : B ∈ Complex.slitPlane := by
      dsimp [B]
      exact Complex.ofReal_mem_slitPlane.2 hbase
    simpa [B] using (tendsto_const_nhds.cpow he hB)

  have hformula : reflectionDOZZ γ μ = fun α =>
      -(B ^ e α) * (Complex.Gamma (-x₁ α) / Complex.Gamma (x₁ α)) *
        (Complex.Gamma (-x₂ α) / Complex.Gamma (x₂ α)) := by
    funext α
    simp [reflectionDOZZ, B, e, d, x₁, x₂]
  rw [hformula]
  simpa using ((hpow.neg).mul hR₁ |>.mul hR₂)

end DOZZ.Proofs
