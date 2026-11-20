module

public import HypoellipticAleksandrov.Measure.HilbertVectorLpAssembly
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10PlateauLocality

/-!
# Principal and companion fields for localized spatial difference quotients

This module packages the cutoff-gradient commutator coordinates into a
Hilbert-vector restricted-`L²` field and defines its principal and companion
combinations with the localized quotient gradient.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem cutoffL2Multiplier_apply_cutoffGradientSpatialDifferenceQuotientL2
    {d : ℕ}
    {Ω innerη outerη innerχ outerχ : Set (PDE.Vec d)}
    {Kη Kχ : ℝ}
    (η : PDE.QuantitativeSmoothCutoff innerη outerη Kη)
    (χ : PDE.QuantitativeSmoothCutoff innerχ outerχ Kχ)
    (hηχ : tsupport η.toFun ⊆ innerχ)
    (hΩ : MeasurableSet Ω) (i k : Fin d) (h : ℝ)
    (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    cutoffL2Multiplier (Ω := Ω) χ
        (cutoffGradientSpatialDifferenceQuotientL2 hΩ η i k h f) =
      cutoffGradientSpatialDifferenceQuotientL2 hΩ η i k h f := by
  apply MeasureTheory.Lp.ext
  filter_upwards [cutoffL2Multiplier_apply_ae χ
    (cutoffGradientSpatialDifferenceQuotientL2 hΩ η i k h f),
    cutoffGradientSpatialDifferenceQuotientL2_apply_ae hΩ η i k h f] with y hχ hη
  rw [hχ, hη]
  by_cases hy : y ∈ tsupport η.toFun
  · rw [χ.eq_one_on_inner y (hηχ hy), one_mul]
  · rw [cutoffGradient_eq_zero_of_not_mem_tsupport η i hy]
    ring

/-- Assemble the cutoff-gradient quotient coordinates as a
Hilbert-vector-valued restricted-`L²` field on `H¹₀`. -/
noncomputable def cutoffGradientSpatialDifferenceQuotientH10CLM
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) :
    H10HilbertGraph hΩ →L[ℝ] PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
  PDE.hilbertVectorLpAssemble fun i =>
    (cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h).comp
      (valueCLM hΩ)

section
variable {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ} (hΩ : IsOpen Ω)
  (η : PDE.QuantitativeSmoothCutoff inner outer K)

/-- The assembled cutoff-gradient field has its literal quotient-safe scalar
coordinate. -/
theorem hilbertVectorLpCoord_cutoffGradientSpatialDifferenceQuotientH10CLM
    (i k : Fin d) (h : ℝ)
    (u : H10HilbertGraph hΩ) :
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
        (cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u) =
      cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
        (valueCLM hΩ u) := PDE.hilbertVectorLpCoord_hilbertVectorLpAssemble _ u i

section
variable (k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω) (hηshift : η.ShiftMapsInto k h Ω)
include k h hηΩ hηshift

/-- The principal field `E = G - W` for the localized spatial quotient. -/
noncomputable def localizedSpatialDifferenceQuotientPrincipalFieldCLM :
    H10HilbertGraph hΩ →L[ℝ] PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
  (gradientCLM hΩ).comp
      (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift) -
    cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h

/-- The companion field `H = G + W` for the localized spatial quotient. -/
noncomputable def localizedSpatialDifferenceQuotientCompanionFieldCLM :
    H10HilbertGraph hΩ →L[ℝ] PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
  (gradientCLM hΩ).comp
      (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift) +
    cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h

end

end

section
variable {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ} (hΩ : IsOpen Ω)
  (η : PDE.QuantitativeSmoothCutoff inner outer K) (i k : Fin d) (h : ℝ)
  (hηΩ : tsupport η.toFun ⊆ Ω) (hηshift : η.ShiftMapsInto k h Ω) (u : H10HilbertGraph hΩ)

/-- The principal-field coordinate is `Gᵢ - Wᵢ`. -/
theorem hilbertVectorLpCoord_localizedSpatialDifferenceQuotientPrincipalFieldCLM :
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
        (localizedSpatialDifferenceQuotientPrincipalFieldCLM
          hΩ η k h hηΩ hηshift u) =
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
          (gradientCLM hΩ
            (localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h hηΩ hηshift u)) -
        cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
          (valueCLM hΩ u) := by
  rw [localizedSpatialDifferenceQuotientPrincipalFieldCLM]
  rw [ContinuousLinearMap.sub_apply]
  rw [map_sub]
  exact congrArg (fun w =>
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
        (gradientCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift u)) - w)
    (hilbertVectorLpCoord_cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η i k h u)

/-- The companion-field coordinate is `Gᵢ + Wᵢ`. -/
theorem hilbertVectorLpCoord_localizedSpatialDifferenceQuotientCompanionFieldCLM :
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
        (localizedSpatialDifferenceQuotientCompanionFieldCLM
          hΩ η k h hηΩ hηshift u) =
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
          (gradientCLM hΩ
            (localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h hηΩ hηshift u)) +
        cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
          (valueCLM hΩ u) := by
  rw [localizedSpatialDifferenceQuotientCompanionFieldCLM]
  rw [ContinuousLinearMap.add_apply]
  rw [map_add]
  exact congrArg (fun w =>
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
        (gradientCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift u)) + w)
    (hilbertVectorLpCoord_cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η i k h u)

end

section
variable {d : ℕ} {Ω innerη outerη innerχ outerχ : Set (PDE.Vec d)} {Kη Kχ : ℝ} (hΩ : IsOpen Ω)
  (η : PDE.QuantitativeSmoothCutoff innerη outerη Kη)
  (χ : PDE.QuantitativeSmoothCutoff innerχ outerχ Kχ) (hηχ : tsupport η.toFun ⊆ innerχ)
  (i k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω) (hηshift : η.ShiftMapsInto k h Ω)
  (u : H10HilbertGraph hΩ)
include innerη outerη innerχ outerχ Kη Kχ hΩ η χ hηχ i k h hηΩ hηshift u

/-- A larger plateau cutoff fixes each principal-field coordinate in
restricted `L²`. -/
theorem cutoffL2Multiplier_apply_principalFieldCoord :
    cutoffL2Multiplier (Ω := Ω) χ
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
          (localizedSpatialDifferenceQuotientPrincipalFieldCLM
            hΩ η k h hηΩ hηshift u)) =
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
        (localizedSpatialDifferenceQuotientPrincipalFieldCLM
          hΩ η k h hηΩ hηshift u) := by
  rw [hilbertVectorLpCoord_localizedSpatialDifferenceQuotientPrincipalFieldCLM, map_sub]
  rw [cutoffL2Multiplier_apply_gradientCoordCLM_localizedSpatialDifferenceQuotientH10CLM
    hΩ η χ hηχ i k h hηΩ hηshift u]
  rw [cutoffL2Multiplier_apply_cutoffGradientSpatialDifferenceQuotientL2
    η χ hηχ hΩ.measurableSet i k h (valueCLM hΩ u)]

/-- A larger plateau cutoff fixes each companion-field coordinate in
restricted `L²`. -/
theorem cutoffL2Multiplier_apply_companionFieldCoord :
    cutoffL2Multiplier (Ω := Ω) χ
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
          (localizedSpatialDifferenceQuotientCompanionFieldCLM
            hΩ η k h hηΩ hηshift u)) =
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
        (localizedSpatialDifferenceQuotientCompanionFieldCLM
          hΩ η k h hηΩ hηshift u) := by
  rw [hilbertVectorLpCoord_localizedSpatialDifferenceQuotientCompanionFieldCLM, map_add]
  rw [cutoffL2Multiplier_apply_gradientCoordCLM_localizedSpatialDifferenceQuotientH10CLM
    hΩ η χ hηχ i k h hηΩ hηshift u]
  rw [cutoffL2Multiplier_apply_cutoffGradientSpatialDifferenceQuotientL2
    η χ hηχ hΩ.measurableSet i k h (valueCLM hΩ u)]

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
