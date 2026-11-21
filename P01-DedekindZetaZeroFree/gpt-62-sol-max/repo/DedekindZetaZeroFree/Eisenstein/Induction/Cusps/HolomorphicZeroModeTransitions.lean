module

public import DedekindZetaZeroFree.Eisenstein.Induction.Cusps.IncomingSheetEvaluation
public import DedekindZetaZeroFree.Eisenstein.Induction.Spherical.CompactJetHolomorphy

@[expose] public section

noncomputable section
open scoped Classical NumberField

namespace DedekindZetaZeroFree.KPContFlatCuspCoefficientTransition

open KPContFlatCuspIncomingEvaluation

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable (a : Cusps F ζ hζ C R P H U)

def zeroFiberEvaluation : ZeroFiber F ζ hζ C R P H U a →ₗ[ℂ] ℂ where
  toFun f := f.val 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl





variable {S : Type*} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]

 def stageCoordinates : S ≃ₗ[ℂ] (Fin (Module.finrank ℂ S) → ℂ) :=
  (Module.finBasis ℂ S).equivFun

 abbrev stageNormedAddCommGroup : NormedAddCommGroup S :=
  NormedAddCommGroup.induced _ _ (stageCoordinates (S := S)).toLinearMap
    (stageCoordinates (S := S)).injective

attribute [local instance] stageNormedAddCommGroup

 abbrev stageNormedSpace : NormedSpace ℂ S :=
  NormedSpace.induced ℂ _ _ (stageCoordinates (S := S)).toLinearMap

attribute [local instance] stageNormedSpace

variable (ι : S →ₗ[ℂ] KPContFlatCommonLevelKernel.CommonSphericalStage F ζ hζ U)

def frameCoefficient (shape : KPCuspCharts.Shape F) (s : ℂ) :
    S →L[ℂ] ZeroFiber F ζ hζ C R P H U a :=
  ((zeroProjection F ζ hζ C R P H U a).comp
    (sheetEvaluation F ζ hζ C R P H U a ι s)).toContinuousLinearMap





 instance instFintypeRootsOfUnity : Fintype (rootsOfUnity 3 F) :=
  Fintype.ofFinite _





end DedekindZetaZeroFree.KPContFlatCuspCoefficientTransition

namespace DedekindZetaZeroFree

end DedekindZetaZeroFree

end
