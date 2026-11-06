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

variable {d : ℕ}



/-- Assemble the cutoff-gradient quotient coordinates as a
Hilbert-vector-valued restricted-`L²` field on `H¹₀`. -/
def cutoffGradientSpatialDifferenceQuotientH10CLM
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) :
    H10HilbertGraph hΩ →L[ℝ] PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
  PDE.hilbertVectorLpAssemble fun i =>
    (cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h).comp
      (valueCLM hΩ)

/-- The assembled cutoff-gradient field has its literal quotient-safe scalar
coordinate. -/
theorem hilbertVectorLpCoord_cutoffGradientSpatialDifferenceQuotientH10CLM
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (i k : Fin d) (h : ℝ)
    (u : H10HilbertGraph hΩ) :
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
        (cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u) =
      cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
        (valueCLM hΩ u) := PDE.hilbertVectorLpCoord_hilbertVectorLpAssemble _ u i

/-- The principal field `E = G - W` for the localized spatial quotient. -/
def localizedSpatialDifferenceQuotientPrincipalFieldCLM
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    H10HilbertGraph hΩ →L[ℝ] PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
  (gradientCLM hΩ).comp
      (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift) -
    cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h

/-- The companion field `H = G + W` for the localized spatial quotient. -/
def localizedSpatialDifferenceQuotientCompanionFieldCLM
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    H10HilbertGraph hΩ →L[ℝ] PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
  (gradientCLM hΩ).comp
      (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift) +
    cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h

variable {d : ℕ} {Ω innerη outerη innerχ outerχ : Set (PDE.Vec d)} {Kη Kχ : ℝ} (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff innerη outerη Kη) (χ : PDE.QuantitativeSmoothCutoff innerχ outerχ Kχ)

/-- The principal-field coordinate is `Gᵢ - Wᵢ`. -/
theorem hilbertVectorLpCoord_localizedSpatialDifferenceQuotientPrincipalFieldCLM
     {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (i k : Fin d) (h : ℝ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (u : H10HilbertGraph hΩ) :
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
        (localizedSpatialDifferenceQuotientPrincipalFieldCLM
          hΩ η k h hηΩ hηshift u) =
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
          (gradientCLM hΩ
            (localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h hηΩ hηshift u)) -
        cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
          (valueCLM hΩ u) := by
  rw [localizedSpatialDifferenceQuotientPrincipalFieldCLM, ContinuousLinearMap.sub_apply]
  rw [map_sub]
  exact congrArg _
    (hilbertVectorLpCoord_cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η i k h u)

/-- The companion-field coordinate is `Gᵢ + Wᵢ`. -/
theorem hilbertVectorLpCoord_localizedSpatialDifferenceQuotientCompanionFieldCLM
     {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (i k : Fin d) (h : ℝ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (u : H10HilbertGraph hΩ) :
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
        (localizedSpatialDifferenceQuotientCompanionFieldCLM
          hΩ η k h hηΩ hηshift u) =
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
          (gradientCLM hΩ
            (localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h hηΩ hηshift u)) +
        cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
          (valueCLM hΩ u) := by
  rw [localizedSpatialDifferenceQuotientCompanionFieldCLM, ContinuousLinearMap.add_apply]
  rw [map_add]
  exact congrArg _
    (hilbertVectorLpCoord_cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η i k h u)

/-- A larger plateau cutoff fixes each principal-field coordinate in
restricted `L²`. -/
theorem cutoffL2Multiplier_apply_principalFieldCoord
    
    (hηχ : tsupport η.toFun ⊆ innerχ)
    (i k : Fin d) (h : ℝ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (u : H10HilbertGraph hΩ) :
    cutoffL2Multiplier (Ω := Ω) χ
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
          (localizedSpatialDifferenceQuotientPrincipalFieldCLM
            hΩ η k h hηΩ hηshift u)) =
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
        (localizedSpatialDifferenceQuotientPrincipalFieldCLM
          hΩ η k h hηΩ hηshift u) := by
  rw [hilbertVectorLpCoord_localizedSpatialDifferenceQuotientPrincipalFieldCLM, map_sub]
  rw [cutoffL2Multiplier_apply_gradientCoordCLM_localizedSpatialDifferenceQuotientH10CLM
    hΩ η χ hηχ]
  rw [cutoffL2Multiplier_apply_cutoffGradientSpatialDifferenceQuotientL2
    η χ hηχ]

/-- A larger plateau cutoff fixes each companion-field coordinate in
restricted `L²`. -/
theorem cutoffL2Multiplier_apply_companionFieldCoord
    
    (hηχ : tsupport η.toFun ⊆ innerχ)
    (i k : Fin d) (h : ℝ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (u : H10HilbertGraph hΩ) :
    cutoffL2Multiplier (Ω := Ω) χ
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
          (localizedSpatialDifferenceQuotientCompanionFieldCLM
            hΩ η k h hηΩ hηshift u)) =
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
        (localizedSpatialDifferenceQuotientCompanionFieldCLM
          hΩ η k h hηΩ hηshift u) := by
  rw [hilbertVectorLpCoord_localizedSpatialDifferenceQuotientCompanionFieldCLM, map_add]
  rw [cutoffL2Multiplier_apply_gradientCoordCLM_localizedSpatialDifferenceQuotientH10CLM
    hΩ η χ hηχ]
  rw [cutoffL2Multiplier_apply_cutoffGradientSpatialDifferenceQuotientL2
    η χ hηχ]

end HypoellipticAleksandrov.Parabolic.Dirichlet
