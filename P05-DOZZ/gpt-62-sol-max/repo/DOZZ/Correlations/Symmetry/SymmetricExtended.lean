/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Symmetry.ReflectionMomentSwap
public import DOZZ.Correlations.Residue.FullFromUnit
@[expose] public section
open MeasureTheory
namespace DOZZ.Proofs

/-- Extended-domain permutation symmetry, with affine re-pinning and correlated Gaussian tilt
for the first--second swap, and the inversion law `DOZZ.equatorGFF_GMC_inversion_law` for the
first--third swap. -/
theorem unitVolumeStructureConstant_symmetric_extended
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hα : ExtendedSeiberg3 γ α₁ α₂ α₃) :
    unitVolumeStructureConstant P M γ α₁ α₂ α₃ = unitVolumeStructureConstant P M γ α₂ α₁ α₃ ∧
      unitVolumeStructureConstant P M γ α₁ α₂ α₃ = unitVolumeStructureConstant P M γ α₁ α₃ α₂ ∧
      unitVolumeStructureConstant P M γ α₁ α₂ α₃ = unitVolumeStructureConstant P M γ α₃ α₂ α₁ := by
  rcases hα with ⟨_, _, _, _⟩
  have h12 := unitVolumeStructureConstant_swap12 P X M γ α₁ α₂ α₃ hγ hγ2 hX hM
  have h13 := unitVolumeStructureConstant_swap13 P X M γ α₁ α₂ α₃ hγ hγ2 hX hM
  refine ⟨h12, ?_, h13⟩
  exact h13.trans ((unitVolumeStructureConstant_swap12 P X M γ α₃ α₂ α₁ hγ hγ2 hX hM).trans
    (unitVolumeStructureConstant_swap13 P X M γ α₂ α₃ α₁ hγ hγ2 hX hM))

/-- Swapping the first two charges of a structure constant in the extended Seiberg domain. -/
theorem structureConstant_swap12 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) {γ μ a b c : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) (h : ExtendedSeiberg3 γ a b c) :
    structureConstant P M γ μ a b c = structureConstant P M γ μ b a c := by
  rw [residue_structureConstant_eq_unitVolume, residue_structureConstant_eq_unitVolume,
    (unitVolumeStructureConstant_symmetric_extended P X M γ a b c hγ hγ2 hX hM h).1,
    show sExp γ b a c = sExp γ a b c by unfold sExp; ring_nf]

/-- Charges below `Q` with positive zero mode satisfy the extended Seiberg bounds. -/
theorem extendedSeiberg3_of_sExp_pos {γ α₁ α₂ α₃ : ℝ} (hγ : 0 < γ)
    (h₁ : α₁ < Q γ) (h₂ : α₂ < Q γ) (h₃ : α₃ < Q γ) (hs : 0 < sExp γ α₁ α₂ α₃) :
    ExtendedSeiberg3 γ α₁ α₂ α₃ := by
  refine ⟨h₁, h₂, h₃, ?_⟩
  have h2γ  := div_pos two_pos hγ
  have hmin := lt_min (show (0 : ℝ) < 4 / γ ^ 2 by positivity)
    (lt_min (mul_pos h2γ (sub_pos.mpr h₁)) (lt_min (mul_pos h2γ (sub_pos.mpr h₂))
      (mul_pos h2γ (sub_pos.mpr h₃))))
  linarith

end DOZZ.Proofs
