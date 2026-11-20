module
public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.ArchSliceGeometry

public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.CasimirParameterJets

@[expose] public section

noncomputable section
open scoped NumberField Classical
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualScalarCasimirTransport
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem insertion_commutes_finitePart
    (r : KPSmoothActualFlowData.GInfinity F)
    (a : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    Commute (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ r) a.val := by apply @DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal.insertion_commutes_finite <;> assumption

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualScalarCasimirTransport

end

section

noncomputable section
open scoped NumberField Classical
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualScalarCasimirTransport

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

theorem insertion_commutes_finiteRepresentative
    (r : KPSmoothActualFlowData.GInfinity F)
    (a : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    Commute (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ r) a.val := by apply @DedekindZetaZeroFree.KPMsActualCuspSource.insertion_commutes <;> assumption

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualScalarCasimirTransport

end
end
