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

/- An affine function with nonzero slope avoids all nonpositive integer poles
outside a codiscrete set. -/
theorem eventually_affine_ne_neg_nat {c d} (hc : c ≠ 0) :
    ∀ᶠ α : ℂ in codiscrete ℂ, ∀ n : ℕ, c * α + d ≠ -(n : ℂ) := by
  let f : ℕ → ℂ := fun n => -(c⁻¹) * (n : ℂ) - d / c
  have hf : IsClosedEmbedding f := by
    simpa [f, sub_eq_add_neg, neg_div] using
      closedEmbedding_affine_nat (c := -(c⁻¹)) (d := -d / c)
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

/-- `lFun` is finite and nonzero on an affine argument off a codiscrete set. -/
theorem eventually_affine_lFun_ne_zero {c d} (hc : c ≠ 0) :
    ∀ᶠ α : ℂ in codiscrete ℂ, lFun (c * α + d) ≠ 0 := by
  have hnum := eventually_affine_ne_neg_nat (c := c) (d := d) hc
  have hden := eventually_affine_ne_neg_nat (c := -c) (d := 1 - d)
    (neg_ne_zero.mpr hc)
  filter_upwards [hnum, hden] with α hnum hden
  unfold lFun
  exact div_ne_zero (Complex.Gamma_ne_zero hnum) (Complex.Gamma_ne_zero (by intro n hn; apply hden n; convert hn using 1; ring))

/- Every affine pullback of a nontrivial entire Upsilon is nonzero off a
codiscrete set. -/
theorem eventually_upsilon_affine_ne_zero {γ : ℝ} {U}
    (hγ : 0 < γ) (hU : IsUpsilon γ U) {c d} (hc : c ≠ 0) :
    ∀ᶠ α : ℂ in codiscrete ℂ, U (c * α + d) ≠ 0 := by
  let f : ℂ → ℂ := fun α => U (c * α + d)
  have hf : AnalyticOnNhd ℂ f Set.univ := by
    intro α hα
    change AnalyticAt ℂ (fun x : ℂ => U (c * x + d)) α
    exact AnalyticAt.comp (f := fun x : ℂ => c * x + d) (g := U) (x := α)
      (hU.1.analyticAt (c * α + d)) (by fun_prop)
  let α₀ : ℂ := ((Q γ : ℂ) / 2 - d) / c
  have harg : c * α₀ + d = (Q γ : ℂ) / 2 := by
    dsimp [α₀]
    field_simp [hc]
    ring
  filter_upwards [(hf.preimage_zero_mem_codiscrete (by rw [show f α₀ = U (c * α₀ + d) by rfl, harg, (IsUpsilon.center hγ hU)]; norm_num))] with α hα
  exact hα

/-- The special value `l(γ²/4)` is the corresponding real Gamma ratio. -/
theorem lFun_gammaSq_real (γ : ℝ) :
    lFun ((γ : ℂ) ^ 2 / 4) =
      ((Real.Gamma (γ ^ 2 / 4) / Real.Gamma (1 - γ ^ 2 / 4) : ℝ) : ℂ) := by
  rw [(show ((γ : ℂ) ^ 2 / 4) = ((γ ^ 2 / 4 : ℝ) : ℂ) by push_cast; ring)]
  unfold lFun
  rw [Complex.Gamma_ofReal, (show Complex.Gamma (1 - (γ ^ 2 / 4 : ℝ)) = (Real.Gamma (1 - γ ^ 2 / 4) : ℂ) by convert Complex.Gamma_ofReal (1 - γ ^ 2 / 4) using 1; simp)]
  exact (Complex.ofReal_div _ _).symm

/-- The DOZZ base `dozzBase γ μ` is positive on the physical parameter range. -/
theorem dozzBase_pos {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ) :
    0 < dozzBase γ μ := by
  rw [dozzBase, lFun_gammaSq_real]
  simp only [Complex.ofReal_re]
  exact mul_pos (mul_pos Real.pi_pos hμ)
    (div_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.Gamma_pos_of_pos (by nlinarith)))

/-- The reflected `lFun` factors multiply to the reciprocal square. -/
theorem lFun_mul_neg {q} (hq : q ≠ 0)
    (hΓq : Complex.Gamma q ≠ 0) (hΓnegq : Complex.Gamma (-q) ≠ 0) :
    lFun q * lFun (-q) = -1 / q ^ 2 := by
  unfold lFun
  rw [(show Complex.Gamma (1 - q) = -q * Complex.Gamma (-q) by simpa [sub_eq_add_neg, add_comm] using Complex.Gamma_add_one (-q) (neg_ne_zero.mpr hq)), show 1 - -q = 1 + q by ring, (show Complex.Gamma (1 + q) = q * Complex.Gamma q by simpa [add_comm] using Complex.Gamma_add_one q hq)]
  field_simp [hq, hΓq, hΓnegq]

end DOZZ.Proofs

end
