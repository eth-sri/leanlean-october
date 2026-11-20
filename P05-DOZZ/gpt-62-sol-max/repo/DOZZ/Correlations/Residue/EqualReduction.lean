/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.UnequalReduction
public import DOZZ.Correlations.Residue.EqualDecomposition

/-! The equal-charge unit-volume residue of the three-to-two residue bridge, reduced solely to the
exact two-insertion tail. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Classical
namespace DOZZ.Proofs

/-- The coalesced two-insertion estimate gives the factor-four unit-volume residue. All
remaining moment, complement and chart obligations are supplied by proved source helpers. -/
theorem residue_unit_equal_of_twoInsertion_estimate
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ α Rbar dT : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : γ / 2 < α) (hαQ : α < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) (hdT : 0 < dT)
    (htail : ∀ θ : ℝ, 0 < θ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ ε, 0 < ε → ε < dT → ∀ t : ℝ, 1 ≤ t →
        |(P {ω | ENNReal.ofReal t <
            localSingularMass M (residueLocalWeight γ (2 * α + ε) α 7) 3 γ α ω +
            localSingularMass M (residueLocalWeight γ (2 * α + ε) α 3) 7 γ α ω}).toReal -
          (oneInsertionTailCoefficient γ α 3 (residueLocalWeight γ (2 * α + ε) α 7 3) Rbar * t ^ (-reflectionExponent γ α) +
           oneInsertionTailCoefficient γ α 7 (residueLocalWeight γ (2 * α + ε) α 3 7) Rbar * t ^ (-reflectionExponent γ α))| ≤
          C * t ^ (-(twoInsertionTailCeiling γ α α - θ))) :
    Tendsto (fun ε : ℝ => ε * unitVolumeStructureConstant P M γ ε α α)
      (𝓝[>] 0) (𝓝 (4 * reflectionExponent γ α * Rbar)) := by
  let _ : IsProbabilityMeasure P := hX.1
  let p := reflectionExponent γ α
  have hp := (residue_critical_order_bounds γ α hγ hα hαQ).1
  let θ := (twoInsertionTailCeiling γ α α - p) / 2
  have hθ : 0 < θ := div_pos (sub_pos.mpr (residue_equal_twoInsertionTailCeiling_gt γ α hγ hα hαQ)) (by norm_num)
  have hexp : -(twoInsertionTailCeiling γ α α - θ) = -p - θ := by dsimp only [θ]; ring
  obtain ⟨C, hC, hCb⟩ := htail θ hθ
  obtain ⟨dR, ρ, hdR, hρ, K, hK, hKb⟩ := residue_equal_complement_moment_uniform
    P X M γ α hγ hγ2 hX hM hα hαQ
  let A : ℝ → Ω → ℝ≥0∞ := fun ε ω =>
    localSingularMass M (residueLocalWeight γ (2 * α + ε) α 7) 3 γ α ω +
    localSingularMass M (residueLocalWeight γ (2 * α + ε) α 3) 7 γ α ω
  let R : ℝ → Ω → ℝ≥0∞ := fun ε ω => ∫⁻ x, if ∀ k : Fin 2, x ∉ Metric.ball (![3, 7] k) 1 then
    coulombWeight γ ![α, α] ![3, 7] ε x else 0 ∂M ω
  let c : ℝ → ℝ := fun ε =>
    oneInsertionTailCoefficient γ α 3 (residueLocalWeight γ (2 * α + ε) α 7 3) Rbar +
    oneInsertionTailCoefficient γ α 7 (residueLocalWeight γ (2 * α + ε) α 3 7) Rbar
  have hA (ε : ℝ) : AEMeasurable (A ε) P :=
    (localSingularMass_aemeasurable P X hX γ hγ hγ2 M hM _
      (by unfold residueLocalWeight; fun_prop) _ _).add
    (localSingularMass_aemeasurable P X hX γ hγ hγ2 M hM _
      (by unfold residueLocalWeight; fun_prop) _ _)
  have hR (ε : ℝ) : AEMeasurable (R ε) P := by
    have hset : MeasurableSet {x : ℂ | ∀ k : Fin 2, x ∉ Metric.ball (![3, 7] k) 1} := by
      have hs : {x : ℂ | ∀ k : Fin 2, x ∉ Metric.ball (![3, 7] k) 1} =
          (Metric.ball (3 : ℂ) 1)ᶜ ∩ (Metric.ball (7 : ℂ) 1)ᶜ := by
        ext x
        simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, mem_inter_iff, mem_compl_iff, mem_ofPred_eq]
      rw [hs]
      exact Metric.isOpen_ball.measurableSet.compl.inter Metric.isOpen_ball.measurableSet.compl
    exact (Measure.measurable_lintegral (Measurable.ite hset (measurable_coulombWeight _ _ _ _) measurable_const)).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM)
  have hatoms : ∀ᵐ ω ∂P, M ω {3} = 0 ∧ M ω {7} = 0 :=
    (gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 3).and
      (gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 7)
  have hdecomp (ε : ℝ) : ∀ᵐ ω ∂P,
      coulombMass γ (M ω) ![α, α] ![3, 7] ε = A ε ω + R ε ω := by
    filter_upwards [hatoms] with ω hω
    exact residue_equal_mass_decomposition M ω γ α ε hω.1 hω.2
  have hc₁ := residue_chart_tail_coefficient_limit γ α α Rbar hγ.ne' 3 7 (by norm_num) (by norm_num) (by norm_num)
  have hc₂ := residue_chart_tail_coefficient_limit γ α α Rbar hγ.ne' 7 3 (by norm_num) (by norm_num) (by norm_num)
  have hn₁ : ‖(3 : ℂ) - 7‖ = 4 := by norm_num
  have hn₂ : ‖(7 : ℂ) - 3‖ = 4 := by norm_num
  have hc := hc₁.add hc₂
  rw [hn₁, hn₂] at hc
  have hh := residue_chart_limit_of_tail_and_complement P A R
    (fun ε ω => coulombMass γ (M ω) ![α, α] ![3, 7] ε) c _ p γ θ C dT dR (p + ρ) K
    hp hγ hθ hC hdT hdR (lt_add_of_pos_right _ hρ) hK hA hR hdecomp hc
    (fun ε he₀ he t ht => by simpa only [← add_mul, hexp] using hCb ε he₀ he t ht) hKb
  have hm : γ * p * ((4 : ℝ) ^ (-(γ * α * p)) * Rbar + (4 : ℝ) ^ (-(γ * α * p)) * Rbar) =
      2 * γ * p * (4 : ℝ) ^ (-(γ * α * p)) * Rbar := by ring
  rw [hm] at hh
  have hunit := residue_unit_limit_from_chart_limit P X M γ α α 2 Rbar hγ hγ2 hX hM
    (by simpa only [p, ENNReal.rpow_eq_pow, sub_self, zero_add] using hh)
  simpa only [sub_self, zero_add, show (2 : ℝ) * 2 = 4 by norm_num] using hunit

end DOZZ.Proofs
