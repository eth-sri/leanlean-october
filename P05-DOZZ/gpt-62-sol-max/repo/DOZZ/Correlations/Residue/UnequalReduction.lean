/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.TailCoefficient
public import DOZZ.Correlations.Residue.TailMargins
public import DOZZ.Correlations.Tails.SingularMassMeasurability
public import DOZZ.Correlations.Residue.ExtendedAddition
public import DOZZ.Correlations.Residue.ComplementUniform
public import DOZZ.Correlations.Residue.MassDecomposition
public import DOZZ.Correlations.Residue.ChartLimit

/-! The full unequal-charge unit-volume residue (erratum K30, see docs/ERRATA-AND-DEVIATIONS.md),
reduced solely to the exact insertion tail. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Classical
namespace DOZZ.Proofs

/-- All moment, complement, chart and normalization steps of the unequal-charge residue are
proved. The remaining input is the one-insertion estimate, uniform in the actual epsilon family. -/
theorem residue_unit_unequal_of_oneInsertion_estimate
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ α2 α3 Rbar η dT C : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα2 : 0 < α2) (hα23 : α2 < α3)
    (hα3 : γ / 2 < α3) (hα3Q : α3 < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hη : 0 < η) (hdT : 0 < dT) (hC : 0 ≤ C)
    (htail : ∀ ε, 0 < ε → ε < dT → ∀ t : ℝ, 1 ≤ t →
      |(P {ω | ENNReal.ofReal t < localSingularMass M
        (residueLocalWeight γ (2 * α3 + ε) α2 7) 3 γ α3 ω}).toReal -
        oneInsertionTailCoefficient γ α3 3 (residueLocalWeight γ (2 * α3 + ε) α2 7 3) Rbar *
          t ^ (-reflectionExponent γ α3)| ≤ C * t ^ (-reflectionExponent γ α3 - η)) :
    Tendsto (fun ε : ℝ => ε * unitVolumeStructureConstant P M γ
      (α3 - α2 + ε) α2 α3) (𝓝[>] 0) (𝓝 (2 * reflectionExponent γ α3 * Rbar)) := by
  let _ : IsProbabilityMeasure P := hX.1
  let p := reflectionExponent γ α3
  have hp := (residue_critical_order_bounds γ α3 hγ hα3 hα3Q).1
  obtain ⟨dR, ρ, hdR, hρ, K, hK, hKb⟩ := residue_unequal_complement_moment_uniform
    P X M γ α2 α3 hγ hγ2 hX hM hα2 hα23 hα3 hα3Q
  let A : ℝ → Ω → ℝ≥0∞ := fun ε =>
    localSingularMass M (residueLocalWeight γ (2 * α3 + ε) α2 7) 3 γ α3
  let R  := fun ε ω => ∫⁻ x, if x ∉ Metric.ball (3 : ℂ) 1 then
    coulombWeight γ ![α3, α2] ![3, 7] (α3 - α2 + ε) x else 0 ∂M ω
  let c ε := oneInsertionTailCoefficient γ α3 3 (residueLocalWeight γ (2 * α3 + ε) α2 7 3) Rbar
  have hA (ε : ℝ) : AEMeasurable (A ε) P :=
    localSingularMass_aemeasurable P X hX γ hγ hγ2 M hM _
      (by unfold residueLocalWeight; fun_prop) _ _
  have hR (ε : ℝ) : AEMeasurable (R ε) P := by
    exact (Measure.measurable_lintegral (Measurable.ite Metric.isOpen_ball.measurableSet.compl (measurable_coulombWeight _ _ _ _) measurable_const)).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM)
  have hatoms  :=
    (gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 3).and
      (gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 7)
  have hdecomp (ε : ℝ) : ∀ᵐ ω ∂P,
      coulombMass γ (M ω) ![α3, α2] ![3, 7] (α3 - α2 + ε) = A ε ω + R ε ω := by
    filter_upwards [hatoms] with ω hω
    rw [residue_mass_decomposition γ α3 α2 (α3 - α2 + ε) 3 7 (by norm_num) (by norm_num) (by norm_num)
      (M ω) hω.1 hω.2]
    have hS : α3 + α2 + (α3 - α2 + ε) = 2 * α3 + ε := by ring
    rw [hS]
    rfl
  have hc := residue_chart_tail_coefficient_limit γ α3 α2 Rbar hγ.ne' 3 7
    (by norm_num) (by norm_num) (by norm_num)
  rw [show ‖(3 : ℂ) - 7‖ = 4 by norm_num] at hc
  have hh := residue_chart_limit_of_tail_and_complement P A R
    (fun ε ω => coulombMass γ (M ω) ![α3, α2] ![3, 7] (α3 - α2 + ε)) c _ p γ η C dT dR (p + ρ) K
    hp hγ hη hC hdT hdR (lt_add_of_pos_right _ hρ) hK hA hR hdecomp hc htail hKb
  simpa only [mul_one] using residue_unit_limit_from_chart_limit P X M γ α2 α3 1 Rbar hγ hγ2 hX hM
    (by simpa only [p, ENNReal.rpow_eq_pow, one_mul, mul_assoc] using hh)

end DOZZ.Proofs
