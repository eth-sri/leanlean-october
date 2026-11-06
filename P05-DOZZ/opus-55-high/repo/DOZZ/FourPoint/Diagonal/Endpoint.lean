/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Diagonal.MassContinuity
import DOZZ.GMC.SharpMoments.SeibergMoment

/-! The physical reduced four-point function is continuous at zero. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- A negative insertion has a continuous reduced four-point expectation at the
coincident root. The fixed far-disk inverse moment supplies domination. -/
theorem fourPointT_continuousAt_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ χ a b c : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hχ : 0 < χ)
    (ha : a < Q γ) (hb : b < Q γ) (hc : c < Q γ)
    (hs : 2 * Q γ + χ < a + b + c)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ContinuousAt (fun z : ℂ => fourPointT P M γ μ (-χ) a b c z) 0 := by
  let s := fourPointSExp γ (-χ) a b c
  have hsp : 0 < s := by
    dsimp [s, fourPointSExp]
    bound
  have hmass : ∀ᵐ ω ∂P,
      ContinuousAt (fun z : ℂ => bpzMass γ χ a b c 0 (M ω) z) 0 := by
    filter_upwards [bpzMass_lt_top_ae (χ := χ) (α₁ := a) (α₂ := b) (α₃ := c)
      P X hX hγ hγ2 M hM hχ ha hb hc 1 (1 / 2) (by norm_num) (by norm_num)] with ω hω
    exact diagonal_bpzMass_continuousAt_zero γ χ a b c (mul_pos hγ hχ).le (M ω) hω
  have hm (z : ℂ) : AEMeasurable (fun ω => bpzMass γ χ a b c 0 (M ω) z) P :=
    gmc_lintegral_aemeasurable P X hX γ hγ hγ2 M hM _
      (ENNReal.measurable_ofReal.comp (measurable_bpzSoftWeight 0 z))
  obtain ⟨k, hk, hlower⟩ := bpzMass_ge_farBall (γ := γ) (χ := χ) (α₁ := a)
    (α₂ := b) (α₃ := c) 1 zero_le_one
  let bound : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (k ^ (-s)) *
    ENNReal.rpow (M ω (bpzFarBall 1)) (-s)
  have hboundfin : ∫⁻ ω, bound ω ∂P < ⊤ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (bpz_farBall_negMoment_lt_top P X hX hγ hγ2 M hM 1 s hsp.le)
  have hbnd (z : ℂ) (hz : ‖z‖ ≤ 1) ω :
      ENNReal.rpow (bpzMass γ χ a b c 0 (M ω) z) (-s) ≤ bound ω := by
    have hfinite : M ω (bpzFarBall 1) ≠ ⊤ := by
      have _ := hM.1 ω
      simp
    exact bpz_rpow_neg_le_of_le hk hfinite
      (hlower z hz 0 le_rfl zero_le_one (M ω)) s hsp.le
  have hmoment : Tendsto (fun z : ℂ => ∫⁻ ω,
      ENNReal.rpow (bpzMass γ χ a b c 0 (M ω) z) (-s) ∂P) (𝓝 0)
      (𝓝 (∫⁻ ω, ENNReal.rpow (bpzMass γ χ a b c 0 (M ω) 0) (-s) ∂P)) := by
    apply tendsto_lintegral_filter_of_dominated_convergence' bound
    · exact Eventually.of_forall fun z => (hm z).pow_const (-s)
    · filter_upwards [Metric.ball_mem_nhds 0 zero_lt_one] with z hz
      have hz' := (show ‖z‖ < 1 by
        simpa using hz).le
      simp_all
    · exact hboundfin.ne
    · filter_upwards [hmass] with ω hω
      exact (show Continuous (fun r => ENNReal.rpow r (-s)) from
        ENNReal.continuous_rpow_const).continuousAt.tendsto.comp hω.tendsto
  have hzeroFin : (∫⁻ ω, ENNReal.rpow (bpzMass γ χ a b c 0 (M ω) 0) (-s) ∂P) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono (hbnd 0 (by simp))) hboundfin
  have ht : ContinuousAt (fun z =>
      2 * μ ^ (-s) / γ * Real.Gamma s *
        (∫⁻ ω, ENNReal.rpow (bpzMass γ χ a b c 0 (M ω) z) (-s) ∂P).toReal) 0 :=
    continuousAt_const.mul ((ENNReal.tendsto_toReal hzeroFin.ne).comp hmoment)
  apply ht.congr_of_eventuallyEq
  exact Eventually.of_forall fun z => fourPointT_eq_bpzMass P X hX hγ hγ2 M hM μ z

end DOZZ.Proofs
