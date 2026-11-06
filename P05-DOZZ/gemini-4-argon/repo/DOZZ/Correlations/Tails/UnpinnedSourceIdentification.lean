/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.UnpinnedCutoffIdentity
public import DOZZ.Correlations.Tails.UnpinnedGMC

/-! Source-space identification of the translated unpinned chaos, by unique cutoff limits. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- A compact test supported in the open unit disk has a strict radial margin. -/
theorem compact_test_unit_margin (f : BoundedContinuousFunction ℂ ℝ)
    (hfc : HasCompactSupport (f : ℂ → ℝ))
    (hfU : tsupport (f : ℂ → ℝ) ⊆ Metric.ball 0 1) :
    ∃ ρ : ℝ, ρ < 1 ∧ ∀ x, f x ≠ 0 → ‖x‖ ≤ ρ := by
  by_cases hne : (tsupport (f : ℂ → ℝ)).Nonempty
  · obtain ⟨x, hx, hmax⟩ := hfc.exists_isMaxOn hne continuous_norm.continuousOn
    refine ⟨‖x‖, ?_, fun y hy => hmax (subset_tsupport _ (Function.mem_support.mpr hy))⟩
    simpa only [Metric.mem_ball, dist_zero_right] using hfU hx
  · refine ⟨0, by norm_num, ?_⟩
    intro x hx
    exact False.elim (hne ⟨x, subset_tsupport _ (Function.mem_support.mpr hx)⟩)


/-- Every compact test in the unit chart has a genuine deterministic transferred GMC test. -/
theorem unpinned_source_compact_test
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    Xc (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    z (hz : 2 ≤ ‖z‖) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ)
    (hN : IsAdmissibleGMCVersion P (Metric.ball 0 1) (fun x => normPlus x ^ (-4 : ℝ))
      (fun ω ε x => Xc ω (z+x) (Real.log (1/ε)) - Xc ω z 0) γ N)
    (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ))
    (hfU : tsupport (f : ℂ → ℝ) ⊆ Metric.ball 0 1) :
    ∃ g : BoundedContinuousFunction ℂ ℝ, HasCompactSupport (g : ℂ → ℝ) ∧
      (∀ w, g w = f (w-z) * Real.exp ((γ ^ 2 + 4) * Real.log (normPlus w))) ∧
      (fun ω => ∫ x, f x ∂N ω) =ᵐ[P]
        fun ω => Real.exp (-γ * Xc ω z 0) * ∫ w, g w ∂M ω := by
  have unpinned_source_test_identity (ρ : ℝ) (hρ : ρ < 1) (f : BoundedContinuousFunction ℂ ℝ) (g : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ)) (hfU : tsupport (f : ℂ → ℝ) ⊆ Metric.ball 0 1) (hf : ∀ x, f x ≠ 0 → ‖x‖ ≤ ρ) (hg : ∀ w, g w = f (w-z) * Real.exp ((γ ^ 2 + 4) * Real.log (normPlus w))) : (fun ω => ∫ x, f x ∂N ω) =ᵐ[P] fun ω => Real.exp (-γ * Xc ω z 0) * ∫ w, g w ∂M ω := by
    let : IsProbabilityMeasure P := hX.1
    have hT : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    obtain ⟨L, hL⟩ := eventually_atTop.mp
      ((Real.tendsto_exp_neg_atTop_nhds_zero.comp hT).eventually (gt_mem_nhds (show 0 < 1-ρ by linarith)))
    let t : ℕ → ℝ := fun n => ((L+n : ℕ) : ℝ)
    have ht : Tendsto t atTop atTop := by
      simpa only [t, Nat.add_comm, Function.comp_def] using hT.comp (tendsto_add_atTop_nat L)
    have hb n : ρ + Real.exp (-t n) ≤ 1 := by
      have h := hL (L+n) (Nat.le_add_right L n)
      change Real.exp (-t n) < 1-ρ at h
      linarith
    exact tendstoInMeasure_ae_unique ((hN.2.2.2 f hfc hfU).comp ht) ((tendstoInMeasure_mul_left (fun n ω => ∫ w, g w ∂regularizedGMC P Xc γ (t n) ω) (fun ω => ∫ w, g w ∂M ω) (fun ω => Real.exp (-γ * Xc ω z 0)) (fun n => (DOZZ.Assembly.regularizedGMC_integral_measurable P X hX Xc hc γ (t n) g g.continuous.measurable).aestronglyMeasurable) ((((hc.1 0).comp (measurable_id.prodMk measurable_const)).const_mul (-γ)).exp.aestronglyMeasurable) ((DOZZ.Assembly.isGMCOf_tendstoInMeasure P X hX Xc hc γ M hM g).comp ht)).congr_left (fun n => ae_of_all P fun ω => (unpinned_cutoff_test_identity P X Xc hX hc z hz γ (t n) ρ (hb n) f g hf hg ω).symm))
  obtain ⟨ρ, hρ, hf⟩ := compact_test_unit_margin f hfc hfU
  obtain ⟨g, hgc, hg⟩ := transferred_compact_test z γ f hfc
  exact ⟨g, hgc, hg, unpinned_source_test_identity
    ρ hρ f g hfc hfU hf hg⟩


end DOZZ.Proofs
