module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.NestedCutoffLocality
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientL2
import all HypoellipticAleksandrov.Parabolic.Dirichlet.CutoffGradientSpatialDifferenceQuotientL2
import all HypoellipticAleksandrov.Parabolic.Dirichlet.H10CommutatorSmoothCore

open private HypoellipticAleksandrov.Parabolic.Dirichlet.gradientCoord_localizedSpatialDifferenceQuotientH10CLM_eq from HypoellipticAleksandrov.Parabolic.Dirichlet.H10CommutatorSmoothCore
open private HypoellipticAleksandrov.Parabolic.Dirichlet.cutoffGradient_eq_zero_of_not_mem_tsupport from HypoellipticAleksandrov.Parabolic.Dirichlet.CutoffGradientSpatialDifferenceQuotientL2


/-!
# Plateau locality for localized spatial difference quotients

This module shows that a larger quantitative cutoff acts as the identity on
the value and gradient-coordinate restricted-`L²` classes of a localized
spatial difference quotient whose smaller cutoff is supported in its plateau.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- A smooth cutoff is almost everywhere strongly measurable on restricted volume. -/
theorem cutoffL2Multiplier_aestronglyMeasurable
    {d : ℕ} {Ω inner outer : PDE.VelocityRegion d} {K : ℝ}
    (χ : PDE.QuantitativeSmoothCutoff inner outer K) :
    AEStronglyMeasurable χ.toFun (PDE.volumeOn Ω) :=
  χ.smooth.continuous.aestronglyMeasurable

variable {d : ℕ}

/-- A quantitative cutoff has norm at most one almost everywhere. -/
theorem cutoffL2Multiplier_norm_le_one
     {Ω inner outer : PDE.VelocityRegion d} {K : ℝ}
    (χ : PDE.QuantitativeSmoothCutoff inner outer K) :
    ∀ᵐ y ∂PDE.volumeOn Ω, ‖χ.toFun y‖ ≤ (1 : ℝ) := (cutoff_norm_le_one χ)





variable {Ω inner outer : PDE.VelocityRegion d} {K : ℝ} (χ : PDE.QuantitativeSmoothCutoff inner outer K)

/-- Multiplication by a quantitative spatial cutoff on restricted `L²`. -/
def cutoffL2Multiplier
      :
    PDE.ScalarLp Ω (2 ) →L[ℝ]
      PDE.ScalarLp Ω (2 ) :=
  scalarL2Multiplier χ.toFun (cutoffL2Multiplier_aestronglyMeasurable χ) 1
    zero_le_one (cutoffL2Multiplier_norm_le_one χ)

/-- The cutoff multiplier is represented almost everywhere by pointwise
multiplication. -/
theorem cutoffL2Multiplier_apply_ae

    (f : PDE.ScalarLp Ω (2 )) :
    ⇑(cutoffL2Multiplier  χ f) =ᵐ[PDE.volumeOn Ω]
      fun y => χ y * f y := scalarL2Multiplier_apply_ae χ.toFun
    _ 1 zero_le_one
    _ f

section
variable {Ω innerη outerη innerχ outerχ : PDE.VelocityRegion d} {Kη Kχ : ℝ} (η : PDE.QuantitativeSmoothCutoff innerη outerη Kη) (χ : PDE.QuantitativeSmoothCutoff innerχ outerχ Kχ) (hηχ : tsupport η.toFun ⊆ innerχ) (hΩ : MeasurableSet Ω)

include hηχ
private theorem cutoffL2Multiplier_apply_localizedSpatialDifferenceQuotientL2

     (k : Fin d) (h : ℝ)
    (f : PDE.ScalarLp Ω (2 )) :
    cutoffL2Multiplier  χ
        (localizedSpatialDifferenceQuotientL2 hΩ η k h f) =
      localizedSpatialDifferenceQuotientL2 hΩ η k h f := by
  apply MeasureTheory.Lp.ext
  filter_upwards [cutoffL2Multiplier_apply_ae χ
    (localizedSpatialDifferenceQuotientL2 hΩ η k h f),
    localizedSpatialDifferenceQuotientL2_apply_ae hΩ η k h f] with y hχ hη
  rw [hχ, hη, localizedSpatialDifferenceQuotient_apply]
  by_cases hy : η y = 0
  · simp [hy]
  · rw [χ.eq_one_on_inner y (hηχ (subset_tsupport η.toFun hy)), one_mul]

private theorem
    cutoffL2Multiplier_apply_cutoffGradientSpatialDifferenceQuotientL2

     (i k : Fin d) (h : ℝ)
    (f : PDE.ScalarLp Ω (2 )) :
    cutoffL2Multiplier  χ
        (cutoffGradientSpatialDifferenceQuotientL2 hΩ η i k h f) =
      cutoffGradientSpatialDifferenceQuotientL2 hΩ η i k h f := by
  apply MeasureTheory.Lp.ext
  filter_upwards [cutoffL2Multiplier_apply_ae χ
    (cutoffGradientSpatialDifferenceQuotientL2 hΩ η i k h f),
    cutoffGradientSpatialDifferenceQuotientL2_apply_ae hΩ η i k h f] with y hχ hη
  rw [hχ, hη]
  by_cases hy : y ∈ tsupport η.toFun
  · rw [χ.eq_one_on_inner y (hηχ hy), one_mul]
  · rw [_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.cutoffGradient_eq_zero_of_not_mem_tsupport η i hy]
    ring
end





/-- A larger plateau cutoff fixes every weak-gradient coordinate of the
localized spatial difference quotient in restricted `L²`. -/
theorem
    cutoffL2Multiplier_apply_gradientCoordCLM_localizedSpatialDifferenceQuotientH10CLM

    {Ω innerη outerη innerχ outerχ : PDE.VelocityRegion d}
    {Kη Kχ : ℝ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff innerη outerη Kη)
    (χ : PDE.QuantitativeSmoothCutoff innerχ outerχ Kχ)
    (hηχ : tsupport η.toFun ⊆ innerχ)
    (i k : Fin d) (h : ℝ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (u : H10HilbertGraph hΩ) :
    cutoffL2Multiplier  χ
        (PDE.hilbertVectorLpCoord Ω (2 ) i
          (gradientCLM hΩ
            (localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h hηΩ hηshift u))) =
      PDE.hilbertVectorLpCoord Ω (2 ) i
        (gradientCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h hηΩ hηshift u)) := by
  rw [_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.gradientCoord_localizedSpatialDifferenceQuotientH10CLM_eq
    hΩ η k h hηΩ hηshift i u]
  rw [map_add]
  rw [cutoffL2Multiplier_apply_cutoffGradientSpatialDifferenceQuotientL2
    η χ hηχ hΩ.measurableSet i k h (valueCLM hΩ u)]
  rw [cutoffL2Multiplier_apply_localizedSpatialDifferenceQuotientL2
    η χ hηχ hΩ.measurableSet k h
      (PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ u))]

end HypoellipticAleksandrov.Parabolic.Dirichlet
