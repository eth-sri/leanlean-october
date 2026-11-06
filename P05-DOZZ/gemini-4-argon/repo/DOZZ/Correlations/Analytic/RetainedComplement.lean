/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.CoulombExteriorDecay
public import DOZZ.Correlations.Analytic.RetainedRegions

/-! Open-set bounds for the mass excluded by the retained cutoff. -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs



/-- Subunit moments of the excluded mass are bounded by the sum of the insertion and exterior
moments. -/
theorem retained_complement_moment_le
    {Ω : Type*} [MeasurableSpace Ω] {N}
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf r m : ℝ) (hm : 0 < m) (hm1 : m ≤ 1) :
    (∫⁻ ω, (∫⁻ x in (retainedRegion z r)ᶜ,
      coulombWeight γ α z αinf x ∂M ω) ^ m ∂P) ≤
      (∑ i, ∫⁻ ω, (∫⁻ x in Metric.ball (z i) (2 * Real.exp (-r)),
        coulombWeight γ α z αinf x ∂M ω) ^ m ∂P) +
      ∫⁻ ω, (∫⁻ x in {x : ℂ | Real.exp r / 2 < ‖x‖},
        coulombWeight γ α z αinf x ∂M ω) ^ m ∂P := by
  classical
  have retained_complement_mass_le {N} (μ : Measure ℂ) γ (α : Fin N → ℝ) (z : Fin N → ℂ) αinf r : (∫⁻ x in (retainedRegion z r)ᶜ, coulombWeight γ α z αinf x ∂μ) ≤ (∑ i, ∫⁻ x in Metric.ball (z i) (2 * Real.exp (-r)), coulombWeight γ α z αinf x ∂μ) + ∫⁻ x in {x : ℂ | Real.exp r / 2 < ‖x‖}, coulombWeight γ α z αinf x ∂μ := by
    have retained_complement_cover : (retainedRegion z r)ᶜ ⊆ (⋃ i, Metric.ball (z i) (2 * Real.exp (-r))) ∪ {x : ℂ | Real.exp r / 2 < ‖x‖} := by
      intro x hx
      by_cases hout : ‖x‖ < Real.exp r
      · have hi : ∃ i, ‖x - z i‖ ≤ Real.exp (-r) := by
          by_contra h
          push Not at h
          exact hx ⟨hout, h⟩
        obtain ⟨i, hi⟩ := hi
        apply Or.inl
        apply mem_iUnion.mpr
        refine ⟨i, ?_⟩
        rw [Metric.mem_ball, dist_eq_norm]
        linarith [Real.exp_pos (-r)]
      · apply Or.inr
        have := Real.exp_pos r
        exact lt_of_lt_of_le (by linarith : Real.exp r / 2 < Real.exp r) (le_of_not_gt hout)
    let ν := μ.withDensity (coulombWeight γ α z αinf)
    have he O (hO : MeasurableSet O) :
        ν O = ∫⁻ x in O, coulombWeight γ α z αinf x ∂μ :=
      withDensity_apply _ hO
    rw [← he _ (retainedRegion_isOpen z r).measurableSet.compl]
    calc
      _ ≤ ν ((⋃ i, Metric.ball (z i) (2 * Real.exp (-r))) ∪
          {x : ℂ | Real.exp r / 2 < ‖x‖}) := measure_mono (retained_complement_cover)
      _ ≤ ν (⋃ i, Metric.ball (z i) (2 * Real.exp (-r))) +
          ν {x : ℂ | Real.exp r / 2 < ‖x‖} := measure_union_le _ _
      _ ≤ (∑ i, ν (Metric.ball (z i) (2 * Real.exp (-r)))) +
          ν {x : ℂ | Real.exp r / 2 < ‖x‖} :=
        add_le_add (measure_iUnion_fintype_le ν _) le_rfl
      _ = _ := by
        rw [he _ (isOpen_lt continuous_const continuous_norm).measurableSet]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        exact he _ Metric.isOpen_ball.measurableSet
  let F (i : Fin N) (ω : Ω) := ∫⁻ x in Metric.ball (z i) (2 * Real.exp (-r)),
    coulombWeight γ α z αinf x ∂M ω
  have hF i : AEMeasurable (fun ω => F i ω ^ m) P :=
    (gmc_setLIntegral_aemeasurable P X hX γ hγ hγ2 M hM _
      (measurable_coulombWeight γ α z αinf) _ Metric.isOpen_ball.measurableSet).pow_const m
  calc
    _ ≤ ∫⁻ ω, (∑ i, F i ω ^ m) + (fun ω => ∫⁻ x in {x : ℂ | Real.exp r / 2 < ‖x‖}, coulombWeight γ α z αinf x ∂M ω) ω ^ m ∂P := by
      apply lintegral_mono
      intro ω
      apply (ENNReal.rpow_le_rpow
        (retained_complement_mass_le (M ω) γ α z αinf r) hm.le).trans
      apply (ENNReal.rpow_add_le_add_rpow _ _ hm.le hm1).trans
      apply add_le_add _ le_rfl
      simpa only [tsum_fintype] using
        (ennreal_rpow_tsum_le_tsum_rpow (fun i => F i ω) hm hm1)
    _ = _ := by
      rw [lintegral_add_right' _ ((gmc_setLIntegral_aemeasurable P X hX γ hγ hγ2 M hM _ (measurable_coulombWeight γ α z αinf) _ (isOpen_lt continuous_const continuous_norm).measurableSet).pow_const m), lintegral_finsetSum' Finset.univ (fun i _ => hF i)]

end DOZZ.Proofs
