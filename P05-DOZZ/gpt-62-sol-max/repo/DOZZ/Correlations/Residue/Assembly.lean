/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import DOZZ.Statements.Correlations.OneInsertionTailUniform
import DOZZ.Correlations.SumTail.Assembly

public import DOZZ.Correlations.Residue.EqualReduction
public import DOZZ.Correlations.Residue.UniformFamilies

/-! The unit-volume three-to-two residue bridge on the full smaller-charge domain.
The equal- and unequal-charge cases use the uniform sum and single-insertion tails respectively. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The complete unit-volume residue follows from the exact uniform insertion-tail inputs.
Both witness obligations and the full smaller-charge domain (erratum K30, see
docs/ERRATA-AND-DEVIATIONS.md) are retained. -/
theorem unitVolumeStructureConstant_threeToTwo_residue_bridge
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ α2 α3 : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : 0 < α2 ∧ α2 ≤ α3 ∧ γ / 2 < α3 ∧ α3 < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
      IsSourceLateralProjection P X γ M Z ∧
        IsReflectionData P γ α3 (B α3) Z ∧
        Tendsto (fun ε : ℝ => ε * unitVolumeStructureConstant P M γ
          (α3 - α2 + ε) α2 α3) (𝓝[>] 0)
          (𝓝 (bridgeMultiplicity α2 α3 * reflectionExponent γ α3 * reflectionBarR P γ α3 (B α3) Z)) := by
  have hα3pos : 0 < α3 := lt_trans (by positivity) hα.2.2.1
  have hcharge : ∀ α ∈ ({α3} : Set ℝ), γ / 2 < α ∧ α < Q γ := by
    intro α hαs
    have hh : α = α3 := hαs
    rw [hh]
    exact ⟨hα.2.2.1, hα.2.2.2⟩
  have hpos3 : ∀ z ∈ ({3} : Set ℂ), 2 ≤ ‖z‖ := by
    intro z hz
    have hh : z = 3 := hz
    rw [hh]
    norm_num
  have hpos7 : ∀ z ∈ ({7} : Set ℂ), 2 ≤ ‖z‖ := by
    intro z hz
    have hh : z = 7 := hz
    rw [hh]
    norm_num
  by_cases heq : α2 = α3
  · subst α2
    let F3s : ℂ → Set (ℂ → ℝ) := fun _ => {F | ∃ ε ∈ Icc 0 1, F = residueLocalWeight γ (2 * α3 + ε) α3 7}
    let F7s : ℂ → Set (ℂ → ℝ) := fun _ => {F | ∃ ε ∈ Icc 0 1, F = residueLocalWeight γ (2 * α3 + ε) α3 3}
    obtain ⟨s3, d3, l3, hF3⟩ := residue_localWeight_uniform_family γ (2 * α3) α3 1 hγ.le
      (by positivity) hα3pos.le 3 7 (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨s7, d7, l7, hF7⟩ := residue_localWeight_uniform_family γ (2 * α3) α3 1 hγ.le
      (by positivity) hα3pos.le 7 3 (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨s, d, l, hF3', hF7'⟩ := residue_uniformFamilies_common_bounds
      {3} {7} F3s F7s (1 / 2) s3 d3 l3 s7 d7 l7 hF3 hF7
    have hsep : ∀ z2 ∈ ({3} : Set ℂ), ∀ z3 ∈ ({7} : Set ℂ), 3 ≤ ‖z2 - z3‖ := by
      intro z2 hz2 z3 hz3
      have hh2 : z2 = 3 := hz2
      have hh3 : z3 = 7 := hz3
      rw [hh2, hh3]
      norm_num
    obtain ⟨B, Z, hZ, hB, htail⟩ :=
      twoInsertion_tail_sum_uniform P X M γ hγ hγ2 hX hM {3} {7} isCompact_singleton isCompact_singleton
      hpos3 hpos7 hsep {α3} {α3} isCompact_singleton isCompact_singleton hcharge hcharge
      F3s F7s (1 / 2) s d l hF3' hF7'
    have hlim := residue_unit_equal_of_twoInsertion_estimate P X M γ α3 (reflectionBarR P γ α3 (B α3) Z) 1
      hγ hγ2 hα.2.2.1 hα.2.2.2 hX hM zero_lt_one (by
        intro θ hθ
        obtain ⟨C, hC, hCb⟩ := htail θ hθ
        refine ⟨C, hC, ?_⟩
        intro ε hε hε1 t ht
        exact hCb 3 rfl 7 rfl α3 rfl α3 rfl _ ⟨ε, ⟨hε.le, hε1.le⟩, rfl⟩
          _ ⟨ε, ⟨hε.le, hε1.le⟩, rfl⟩ t ht)
    refine ⟨B, Z, hZ, hB α3 (Or.inl rfl), ?_⟩
    simpa only [bridgeMultiplicity, ite_true, sub_self, zero_add] using hlim
  · have hlt : α2 < α3 := lt_of_le_of_ne hα.2.1 heq
    let Fs : ℂ → Set (ℂ → ℝ) := fun _ => {F | ∃ ε ∈ Icc 0 1, F = residueLocalWeight γ (2 * α3 + ε) α2 7}
    obtain ⟨s, d, l, hF⟩ := residue_localWeight_uniform_family γ (2 * α3) α2 1 hγ.le
      (by positivity) hα.1.le 3 7 (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨B, Z, hZ, hB, htail⟩ :=
      DOZZ.oneInsertion_tail_uniform P X M γ hγ hγ2 hX hM {3} isCompact_singleton hpos3 {α3}
      isCompact_singleton hcharge Fs (1 / 2) s d l hF
    let η := oneInsertionErrorCeiling γ α3 / 2
    have he : 0 < oneInsertionErrorCeiling γ α3 := residue_oneInsertionErrorCeiling_pos γ α3 hγ hα.2.2.1 hα.2.2.2
    have hη : 0 < η := by dsimp only [η]; positivity
    have hηbound : ∀ α ∈ ({α3} : Set ℝ), η < oneInsertionErrorCeiling γ α := by
      intro α hαs
      have hh : α = α3 := hαs
      rw [hh]
      dsimp only [η]
      linarith only [he]
    obtain ⟨C, hC, hCb⟩ := htail η hη hηbound
    have hlim := residue_unit_unequal_of_oneInsertion_estimate P X M γ α2 α3
      (reflectionBarR P γ α3 (B α3) Z) η 1 C hγ hγ2 hα.1 hlt hα.2.2.1 hα.2.2.2 hX hM hη zero_lt_one hC (by
        intro ε hε hε1 t ht
        exact hCb 3 rfl α3 rfl _ ⟨ε, ⟨hε.le, hε1.le⟩, rfl⟩ t ht)
    refine ⟨B, Z, hZ, hB α3 rfl, ?_⟩
    simpa only [bridgeMultiplicity, ite_eq_right heq] using hlim

end DOZZ.Proofs
