module

public import HypoellipticAleksandrov.Measure.HilbertVectorLpAssembly
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10PlateauLocality
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.CutoffGradientSpatialDifferenceQuotientL2
import all HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10PlateauLocality

open private HypoellipticAleksandrov.Parabolic.Dirichlet.cutoffL2Multiplier_apply_cutoffGradientSpatialDifferenceQuotientL2 from HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10PlateauLocality
open private HypoellipticAleksandrov.Parabolic.Dirichlet.cutoffGradient_eq_zero_of_not_mem_tsupport from HypoellipticAleksandrov.Parabolic.Dirichlet.CutoffGradientSpatialDifferenceQuotientL2


/-!
# Principal and companion fields for localized spatial difference quotients

This module packages the cutoff-gradient commutator coordinates into a
Hilbert-vector restricted-`L²` field and defines its principal and companion
combinations with the localized quotient gradient.
-/

@[expose] public section

noncomputable section


open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ}







section
variable {Ω inner outer : PDE.VelocityRegion d} {K : ℝ} (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)

/-- Assemble the cutoff-gradient quotient coordinates as a
Hilbert-vector-valued restricted-`L²` field on `H¹₀`. -/
def cutoffGradientSpatialDifferenceQuotientH10CLM

    (k : Fin d) (h : ℝ) :
    H10HilbertGraph hΩ →L[ℝ] PDE.HilbertVectorLp Ω (2 ) :=
  PDE.hilbertVectorLpAssemble fun i =>
    (cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h).comp
      (valueCLM hΩ)

/-- The assembled cutoff-gradient field has its literal quotient-safe scalar
coordinate. -/
theorem hilbertVectorLpCoord_cutoffGradientSpatialDifferenceQuotientH10CLM

    (i k : Fin d) (h : ℝ)
    (u : H10HilbertGraph hΩ) :
    PDE.hilbertVectorLpCoord Ω (2 ) i
        (cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u) =
      cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
        (valueCLM hΩ u) := PDE.hilbertVectorLpCoord_hilbertVectorLpAssemble _ u i

section
variable (k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω) (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport η.toFun) Ω)

/-- The principal field `E = G - W` for the localized spatial quotient. -/
def localizedSpatialDifferenceQuotientPrincipalFieldCLM

     :
    H10HilbertGraph hΩ →L[ℝ] PDE.HilbertVectorLp Ω (2 ) :=
  (gradientCLM hΩ).comp
      (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift) -
    cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h

/-- The companion field `H = G + W` for the localized spatial quotient. -/
def localizedSpatialDifferenceQuotientCompanionFieldCLM

     :
    H10HilbertGraph hΩ →L[ℝ] PDE.HilbertVectorLp Ω (2 ) :=
  (gradientCLM hΩ).comp
      (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift) +
    cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h
end


variable (i k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω) (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport η.toFun) Ω) (u : H10HilbertGraph hΩ)

/-- The principal-field coordinate is `Gᵢ - Wᵢ`. -/
theorem hilbertVectorLpCoord_localizedSpatialDifferenceQuotientPrincipalFieldCLM

     :
    PDE.hilbertVectorLpCoord Ω (2 ) i
        (localizedSpatialDifferenceQuotientPrincipalFieldCLM
          hΩ η k h hηΩ hηshift u) =
      PDE.hilbertVectorLpCoord Ω (2 ) i
          (gradientCLM hΩ
            (localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h hηΩ hηshift u)) -
        cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
          (valueCLM hΩ u) := by
  rw [localizedSpatialDifferenceQuotientPrincipalFieldCLM]
  rw [ContinuousLinearMap.sub_apply]
  rw [map_sub]
  exact congrArg (fun w =>
    PDE.hilbertVectorLpCoord Ω (2 ) i
        (gradientCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift u)) - w)
    (hilbertVectorLpCoord_cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η i k h u)

/-- The companion-field coordinate is `Gᵢ + Wᵢ`. -/
theorem hilbertVectorLpCoord_localizedSpatialDifferenceQuotientCompanionFieldCLM

     :
    PDE.hilbertVectorLpCoord Ω (2 ) i
        (localizedSpatialDifferenceQuotientCompanionFieldCLM
          hΩ η k h hηΩ hηshift u) =
      PDE.hilbertVectorLpCoord Ω (2 ) i
          (gradientCLM hΩ
            (localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h hηΩ hηshift u)) +
        cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
          (valueCLM hΩ u) := by
  rw [localizedSpatialDifferenceQuotientCompanionFieldCLM]
  rw [ContinuousLinearMap.add_apply]
  rw [map_add]
  exact congrArg (fun w =>
    PDE.hilbertVectorLpCoord Ω (2 ) i
        (gradientCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift u)) + w)
    (hilbertVectorLpCoord_cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η i k h u)
end


variable {Ω innerη outerη innerχ outerχ : PDE.VelocityRegion d} {Kη Kχ : ℝ} (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff innerη outerη Kη) (χ : PDE.QuantitativeSmoothCutoff innerχ outerχ Kχ) (hηχ : tsupport η.toFun ⊆ innerχ) (i k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω) (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport η.toFun) Ω) (u : H10HilbertGraph hΩ)

include hηχ
/-- A larger plateau cutoff fixes each principal-field coordinate in
restricted `L²`. -/
theorem cutoffL2Multiplier_apply_principalFieldCoord

     :
    cutoffL2Multiplier  χ
        (PDE.hilbertVectorLpCoord Ω (2 ) i
          (localizedSpatialDifferenceQuotientPrincipalFieldCLM
            hΩ η k h hηΩ hηshift u)) =
      PDE.hilbertVectorLpCoord Ω (2 ) i
        (localizedSpatialDifferenceQuotientPrincipalFieldCLM
          hΩ η k h hηΩ hηshift u) := by
  rw [hilbertVectorLpCoord_localizedSpatialDifferenceQuotientPrincipalFieldCLM]
  rw [map_sub]
  rw [cutoffL2Multiplier_apply_gradientCoordCLM_localizedSpatialDifferenceQuotientH10CLM
    hΩ η χ hηχ i k h hηΩ hηshift u]
  rw [_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.cutoffL2Multiplier_apply_cutoffGradientSpatialDifferenceQuotientL2
    η χ hηχ hΩ.measurableSet i k h (valueCLM hΩ u)]

/-- A larger plateau cutoff fixes each companion-field coordinate in
restricted `L²`. -/
theorem cutoffL2Multiplier_apply_companionFieldCoord

     :
    cutoffL2Multiplier  χ
        (PDE.hilbertVectorLpCoord Ω (2 ) i
          (localizedSpatialDifferenceQuotientCompanionFieldCLM
            hΩ η k h hηΩ hηshift u)) =
      PDE.hilbertVectorLpCoord Ω (2 ) i
        (localizedSpatialDifferenceQuotientCompanionFieldCLM
          hΩ η k h hηΩ hηshift u) := by
  rw [hilbertVectorLpCoord_localizedSpatialDifferenceQuotientCompanionFieldCLM]
  rw [map_add]
  rw [cutoffL2Multiplier_apply_gradientCoordCLM_localizedSpatialDifferenceQuotientH10CLM
    hΩ η χ hηχ i k h hηΩ hηshift u]
  rw [_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.cutoffL2Multiplier_apply_cutoffGradientSpatialDifferenceQuotientL2
    η χ hηχ hΩ.measurableSet i k h (valueCLM hΩ u)]

end HypoellipticAleksandrov.Parabolic.Dirichlet
