module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CuspCoordinatesAndTruncation

@[expose] public section

noncomputable section
open scoped NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Measurability
open KPAdelicCoverRestrictedProduct

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private alias finiteProjection_local_infinite := DedekindZetaZeroFree.KPMsActualCuspSource.finiteProjection_local_infinite

alias finiteProjection_archimedeanInsertion := DedekindZetaZeroFree.KPMsActualCuspSource.finiteProjection_insertion

theorem finiteProjection_rationalLift (σ : KPCuspArithmetic.PGL2 F) :
    KPCuspGenuineMonodromy.finiteProjection F ζ hζ
      (KPMsClearedTruncationL2.rationalLift F ζ hζ σ) = KPFiniteComponents.diagonal F σ := by apply @DedekindZetaZeroFree.KPMsActualCuspSource.finiteProjection_rationalLift <;> assumption

variable {F ζ hζ}
local instance : MulAction (KPCuspArithmetic.PGL2 F) (KPArch.Space (KPCuspLogShape.dimension F)) :=
  KPCuspSiegel.instMulActionPGL2SpaceDimension F
open KPMsClearedTruncationL2
open KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent
variable {C : ModelData F ζ hζ} {D : Iwasawa F ζ hζ}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
    {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
    {A : KPMsRationalCompactCrossPairing.RawCompactComparison F ζ hζ C D R P H}
    {U : Level F ζ hζ}

end DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Measurability

end
