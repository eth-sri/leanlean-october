/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.Upsilon.StripIdentities
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Topology.MetricSpace.Basic

/-!
# Codiscrete affine loci for the DOZZ identities
-/

@[expose] public section

open Complex Filter Set Topology

namespace DOZZ.Proofs
section
variable {c d : ℂ}
section
variable (hc : c ≠ 0)
include hc

private lemma closedEmbedding_affine_nat :
    IsClosedEmbedding (fun n : ℕ => c * (n : ℂ) + d) := by
  apply Metric.isClosedEmbedding_of_pairwise_le_dist (norm_pos_iff.mpr hc)
  intro m n hmn
  have hnat : (1 : ℝ) ≤ dist m n := Nat.pairwise_one_le_dist hmn
  have hnat' : (1 : ℝ) ≤ |(m : ℝ) - n| := by
    assumption
  have hnorm : ‖(m : ℂ) - n‖ = |(m : ℝ) - n| := by
    norm_cast
  rw [dist_eq_norm]
  calc
    ‖c‖ = ‖c‖ * 1 := by ring
    _ ≤ ‖c‖ * |(m : ℝ) - n| := by simp_all
    _ = ‖c * ((m : ℂ) - n)‖ := by simp_all
    _ = ‖c * (m : ℂ) + d - (c * n + d)‖ := by ring

/- An affine function with nonzero slope avoids all nonpositive integer poles
outside a codiscrete set. -/
theorem eventually_affine_ne_neg_nat :
    ∀ᶠ α : ℂ in codiscrete ℂ, ∀ n : ℕ, c * α + d ≠ -(n : ℂ) := by
  let f : ℕ → ℂ := fun n => -(c⁻¹) * n - d / c
  have hf : IsClosedEmbedding f := by
    simpa [f, sub_eq_add_neg, neg_div] using
      closedEmbedding_affine_nat
        (neg_ne_zero.mpr (inv_ne_zero hc))
  have hbad : (Set.range f)ᶜ ∈ codiscrete ℂ := by
    apply compl_mem_codiscrete_iff.mpr
    exact ⟨hf.isClosed_range, hf.isEmbedding.isInducing.isDiscrete_range⟩
  filter_upwards [hbad] with α hα n
  grind

/-- `lFun` is finite and nonzero on an affine argument off a codiscrete set. -/
theorem eventually_affine_lFun_ne_zero :
    ∀ᶠ α : ℂ in codiscrete ℂ, lFun (c * α + d) ≠ 0 := by
  have hnum := eventually_affine_ne_neg_nat (c := c) (d := d) hc
  have hden := eventually_affine_ne_neg_nat (c := -c) (d := 1 - d)
    (neg_ne_zero.mpr hc)
  filter_upwards [hnum, hden] with α hnum hden
  have hden' : ∀ n : ℕ, 1 - (c * α + d) ≠ -n := by
    grind
  unfold lFun
  grind

end

end

/- Every affine pullback of a nontrivial entire Upsilon is nonzero off a
codiscrete set. -/
theorem eventually_upsilon_affine_ne_zero {γ : ℝ} {U : ℂ → ℂ}
    (hγ : 0 < γ) (hU : IsUpsilon γ U) {c d : ℂ} (hc : c ≠ 0) :
    ∀ᶠ α : ℂ in codiscrete ℂ, U (c * α + d) ≠ 0 := by
  let f : ℂ → ℂ := fun α => U (c * α + d)
  have hf : AnalyticOnNhd ℂ f Set.univ := by
    intro α hα
    exact AnalyticAt.comp
      (hU.1.analyticAt _) (by fun_prop)
  let α₀ := ((Q γ) / 2 - d) / c
  have harg : c * α₀ + d = (Q γ) / 2 := by
    grind
  have hcenter := IsUpsilon.center hγ hU
  have hf₀ : f α₀ ≠ 0 := by
    aesop
  exact hf.preimage_zero_mem_codiscrete hf₀

/-- The special value `l(γ²/4)` is the corresponding real Gamma ratio. -/
theorem lFun_gammaSq_real (γ : ℝ) :
    lFun ((γ : ℂ) ^ 2 / 4) =
      ((Real.Gamma (γ ^ 2 / 4) / Real.Gamma (1 - γ ^ 2 / 4) : ℝ) : ℂ) := by
  have harg : (γ ^ 2 / 4) = ((γ ^ 2 / 4 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg]
  unfold lFun
  have hden : Complex.Gamma (1 - (γ ^ 2 / 4 : ℝ)) =
      (Real.Gamma (1 - γ ^ 2 / 4) : ℂ) := by
    convert Complex.Gamma_ofReal _ using 1
    simp
  rw [Complex.Gamma_ofReal, hden]
  simp

/-- The DOZZ base `dozzBase γ μ` is positive on the physical parameter range. -/
theorem dozzBase_pos {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ) :
    0 < dozzBase γ μ := by
  have hq : 0 < γ ^ 2 / 4 := by positivity
  have hq1 : 0 < 1 - γ ^ 2 / 4 := by nlinarith
  rw [dozzBase, lFun_gammaSq_real]
  simp
  positivity

/-- The reflected `lFun` factors multiply to the reciprocal square. -/
theorem lFun_mul_neg {q : ℂ} (hq : q ≠ 0)
    (hΓq : Complex.Gamma q ≠ 0) (hΓnegq : Complex.Gamma (-q) ≠ 0) :
    lFun q * lFun (-q) = -1 / q ^ 2 := by
  have hrec₁ : Complex.Gamma (1 - q) = -q * Complex.Gamma (-q) := by
    simpa [sub_eq_add_neg, add_comm] using
      Complex.Gamma_add_one (-q) (neg_ne_zero.mpr hq)
  have hrec₂ : Complex.Gamma (1 + q) = q * Complex.Gamma q := by
    simpa [add_comm] using Complex.Gamma_add_one q hq
  unfold lFun
  grind

end DOZZ.Proofs

end
