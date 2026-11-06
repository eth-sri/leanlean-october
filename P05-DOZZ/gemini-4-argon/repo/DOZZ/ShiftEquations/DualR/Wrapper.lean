/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.DualR.Assembly
public import DOZZ.ShiftEquations.Shift.Wrappers
public import DOZZ.ShiftEquations.Gluing.ReflectedWrapper
public import DOZZ.ShiftEquations.Inversion.Reduction
public import DOZZ.ShiftEquations.FirstStrip.Closed

/-!
# The dual shift of `R` from the γ/2 crossing, the gluing, the inversion and the second dual seed

The inputs `DOZZ.reflectionR_first_shift_meromorphic` and
`DOZZ.reflectionBarR_holomorphic_representation` of
`reflectionR_dual_shift_unknown_constant_of_deps` follow from the unit-volume conjunct of the γ/2
crossing `DOZZ.gammaHalf_crossing` alone (`reflectionR_first_shift_meromorphic_of_crossing`,
`reflectionBarR_holomorphic_representation_of_crossing`).
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

theorem reflectionR_dual_shift_unknown_constant_of_crossing_seed
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (M : Ω → Measure ℂ) (γ μ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2)) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hCross : ∀ μ α' ε α : ℝ, 0 < μ → γ / 2 < ε → ε < 2 / γ → α < Q γ → α' < Q γ →
      2 * Q γ < α + α' + ε - γ / 2 →
      unitVolumeStructureConstant P M γ (α' - γ / 2) ε α =
        gammaHalfUnitCrossingMultiplier γ μ α' ε α *
          unitVolumeStructureConstant P M γ α' (ε + γ / 2) α)
    (hSeed : ∀ α ε α' : ℝ, α < Q γ → ε < Q γ → α' < Q γ → 2 * Q γ + 2 / γ < α + ε + α' →
      ∃ Bε Bα : Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧ IsReflectionData P γ ε Bε Z ∧
          IsReflectionData P γ α Bα Z ∧
          reflectionR P γ μ ε Bε Z * structureConstant P M γ μ (2 * Q γ - ε - 2 / γ) α α' =
            dualCrossingL γ ε α α' * reflectionR P γ μ α Bα Z *
              structureConstant P M γ μ ε (2 * Q γ - α - 2 / γ) α') :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α : ℝ, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ R : ℂ → ℂ,
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) =
                  (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              ∃ cγ : ℂ, cγ ≠ 0 ∧
                cγ = ((γ : ℂ) ^ 2 / 4) * (μ * Real.pi : ℂ) * R γ ∧
                ∀ᶠ z in codiscrete ℂ,
                  R z = -cγ * R (z + 2 / γ) /
                    (lFun (-4 / (γ : ℂ) ^ 2) * lFun (2 * z / γ) *
                      lFun (2 + 4 / (γ : ℂ) ^ 2 - 2 * z / γ)) := by
  have hFirstShift := reflectionR_first_shift_meromorphic_of_crossing P X M γ μ hγ hγ2 hμ hX hM hCross
  have hShiftGluing := fun η hη α₂ α₃ hα₂ hα₃ =>
    structureConstant_reflected_shift_and_gluing_of_shifts P X M γ μ η hγ hγ2 hμ hη hX hM α₂ α₃
      hα₂ hα₃ hFirstShift
      (structureConstant_first_shift_strip_unconditional P X M γ μ η hγ hγ2 hμ hη hX hM α₂ α₃ hα₂ hα₃)
  exact reflectionR_dual_shift_unknown_constant_of_deps P X M γ μ hγ hγ2 hγirr hμ hX hM
    hFirstShift
    (fun I _ hI => reflectionBarR_holomorphic_representation_of_crossing P X M γ hγ hγ2 hX hM
      hCross I hI)
    hShiftGluing
    (reflectionR_inversion_meromorphic_of_reflected_shift_and_gluing P X M γ μ hγ hγ2 hμ hX hM hShiftGluing)
    hSeed

end DOZZ.Proofs

end
