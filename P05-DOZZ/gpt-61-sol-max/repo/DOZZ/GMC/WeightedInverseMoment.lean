/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GMC.SharpMoments.ArbitraryCenter
import Mathlib.Tactic

/-! A fixed positive weighted disk controls every inverse moment uniformly. -/
public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Any family of masses retaining the same positively weighted disk has uniform inverse moments. -/
theorem gmc_inverse_moment_uniform_of_disk_lower
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (q w : ℝ) (hq : 0 ≤ q) (hw : 0 < w) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Ω → ℝ≥0∞,
      (∀ ω, ENNReal.ofReal w * M ω (Metric.ball (3 : ℂ) (1 / 8)) ≤ f ω) →
      (∫⁻ ω, f ω ^ (-q) ∂P) ≤ ENNReal.ofReal C := by
  have hb := gmc_ball_moment_lt_top_any_center P X hX γ hγ hγ₂ M hM
    3 (1 / 8) (by norm_num) le_rfl (-q) (lt_of_le_of_lt (neg_nonpos.mpr hq) (by positivity))
  let A := ENNReal.ofReal (w ^ (-q)) * gmcMassMoment P M (Metric.ball (3 : ℂ) (1 / 8)) (-q)
  have hA : A ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb.ne
  refine ⟨A.toReal + 1, by positivity, fun f hf => ?_⟩
  calc
    (∫⁻ ω, f ω ^ (-q) ∂P) ≤
        ∫⁻ ω, ENNReal.ofReal (w ^ (-q)) * M ω (Metric.ball (3 : ℂ) (1 / 8)) ^ (-q) ∂P := by
      apply lintegral_mono
      intro ω
      let _ := hM.1 ω
      have h := ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow (hf ω) hq)
      rwa [← ENNReal.rpow_neg, ← ENNReal.rpow_neg,
        ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _),
        ENNReal.ofReal_rpow_of_pos hw] at h
    _ = A := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (A.toReal + 1) :=
      (ENNReal.ofReal_toReal hA).symm.le.trans (ENNReal.ofReal_le_ofReal (by linarith))

end DOZZ.Proofs
