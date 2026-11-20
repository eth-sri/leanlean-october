/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import DOZZ.Upsilon.StripIdentities

/-!
# Uniqueness of the entire Upsilon continuation
-/

@[expose] public section

open Filter Topology

namespace DOZZ.Proofs

variable {γ : ℝ}

private theorem openStrip_mem_nhds (q : ℝ) (hq : 0 < q) :
    {z : ℂ | 0 < z.re ∧ z.re < q} ∈ 𝓝 ((q : ℂ) / 2) := by
  let S : Set ℂ := {z | 0 < z.re ∧ z.re < q}
  let c := (q : ℂ) / 2
  have hc : c ∈ S := by
    dsimp [c, S]
    simp only [Complex.div_ofNat_re, Complex.ofReal_re]
    constructor <;> linarith
  exact IsOpen.mem_nhds (id (IsOpen.preimage Complex.continuous_re isOpen_Ioo)) hc

/-- Uniqueness of `Υ_{γ/2}` (identity theorem on the strip). -/
theorem IsUpsilon.unique {U V : ℂ → ℂ} (hγ : 0 < γ) (hU : IsUpsilon γ U)
    (hV : IsUpsilon γ V) : U = V := by
  let c := (Q γ : ℂ) / 2
  let S : Set ℂ := {z | 0 < z.re ∧ z.re < Q γ}
  have hS  := openStrip_mem_nhds (Q γ) (by
    unfold Q
    positivity)
  exact AnalyticOnNhd.eq_of_eventuallyEq (fun z x => Differentiable.analyticAt hU.left z)
    (fun z x => Differentiable.analyticAt hV.left z)
    (mp_mem hS
      (univ_mem'
        (id fun z hz => Eq.trans (hU.right z hz.left hz.right) (Eq.symm (hV.right z hz.left hz.right)))))

/-- Reflection symmetry `Υ(Q - z) = Υ(z)`. -/
theorem IsUpsilon.reflect {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hU : IsUpsilon γ U) (z : ℂ) :
    U (Q γ - z) = U z := by
  have hratio : γ / 2 < 2 / γ := by
    apply (div_lt_iff₀ (show (0 : ℝ) < 2 by norm_num)).2
    rw [show 2 / γ * 2 = 4 / γ by ring]
    apply (lt_div_iff₀ hγ).2
    have h1 : 0 < 2 - γ := by linarith
    have h2 : 0 < 2 + γ := by linarith
    have hprod := mul_pos h1 h2
    nlinarith
  have hγQ : γ < Q γ := by
    unfold Q
    linarith
  let S : Set ℂ := {w | 0 < w.re ∧ w.re < Q γ}
  have hS : S ∈ 𝓝 ((Q γ : ℂ) / 2) := by
    simpa [S] using openStrip_mem_nhds (Q γ) (by linarith)
  have hEq : (fun w : ℂ => U ((Q γ : ℂ) - w)) =ᶠ[𝓝 ((Q γ : ℂ) / 2)] U := by
    filter_upwards [hS] with w hw
    dsimp [S] at hw
    have hw' : 0 < ((Q γ : ℂ) - w).re ∧ ((Q γ : ℂ) - w).re < Q γ := by
      simp 
      constructor <;> linarith
    rw [hU.2 ((Q γ : ℂ) - w) hw'.1 hw'.2, upsilonLog_reflect γ w hw.1 hw.2, (hU.2 w hw.1 hw.2).symm]
  exact congrFun
    (AnalyticOnNhd.eq_of_eventuallyEq
      (fun w x =>
        Differentiable.analyticAt
          (Differentiable.comp hU.left (Differentiable.const_sub differentiable_id ↑(Q γ))) w)
      (fun w x => Differentiable.analyticAt hU.left w) hEq)
    z

end DOZZ.Proofs
