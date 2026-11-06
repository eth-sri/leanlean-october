/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GMC.WeightedInverseMoment
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Tactic

/-! A shared dominated-convergence argument for masses retaining a fixed weighted disk. -/
public section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

theorem gmc_inverse_moment_tendsto_of_disk_lower
    {Ω ι : Type*} [MeasurableSpace Ω] {l : Filter ι} [l.IsCountablyGenerated]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (q w : ℝ) (hq : 0 ≤ q) (hw : 0 < w) (f : ι → Ω → ℝ≥0∞) (g : Ω → ℝ≥0∞)
    (hm : ∀ᶠ i in l, AEMeasurable (f i) P)
    (hb : ∀ᶠ i in l, ∀ ω, ENNReal.ofReal w * M ω (Metric.ball (3 : ℂ) (1/8)) ≤ f i ω)
    (hl : ∀ᵐ ω ∂P, Tendsto (fun i => f i ω) l (𝓝 (g ω))) :
    Tendsto (fun i => ∫⁻ ω, f i ω ^(-q) ∂P) l (𝓝 (∫⁻ ω, g ω ^(-q) ∂P)) := by
  let G := fun ω => ENNReal.ofReal (w ^(-q))*M ω (Metric.ball (3 : ℂ) (1/8)) ^(-q)
  have hbound : ∀ᶠ i in l, ∀ᵐ ω ∂P, f i ω ^(-q) ≤ G ω := by
    filter_upwards [hb] with i hi
    apply ae_of_all
    intro ω
    let _ := hM.1 ω
    have h := ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow (hi ω) hq)
    rwa [← ENNReal.rpow_neg, ← ENNReal.rpow_neg,
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _),
      ENNReal.ofReal_rpow_of_pos hw] at h
  have hfinite : (∫⁻ ω, G ω ∂P) ≠ ⊤ := by
    have h := gmc_ball_moment_lt_top_any_center P X hX γ hγ hγ₂ M hM
      3 (1/8) (by norm_num) le_rfl (-q)
      (lt_of_le_of_lt (neg_nonpos.mpr hq) (by positivity))
    rw [show (∫⁻ ω, G ω ∂P) = ENNReal.ofReal (w ^(-q))*
      (∫⁻ ω, M ω (Metric.ball (3 : ℂ) (1/8)) ^(-q) ∂P) from
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h.ne
  exact tendsto_lintegral_filter_of_dominated_convergence' G
    (hm.mono fun _ h => h.pow_const (-q)) hbound hfinite
    (hl.mono fun _ h => ENNReal.continuous_rpow_const.tendsto _ |>.comp h)

end DOZZ.Proofs
