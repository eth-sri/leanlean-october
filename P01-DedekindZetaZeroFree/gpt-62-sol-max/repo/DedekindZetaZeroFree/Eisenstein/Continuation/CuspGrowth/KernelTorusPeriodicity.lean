module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.CasimirParameterJets
public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspGrowth.CompactCrossExponentialBound

@[expose] public section

noncomputable section
open scoped Classical NumberField
set_option maxHeartbeats 1200000
namespace DedekindZetaZeroFree.KPContinuation.ChamberModerateGrowth
open KPContFlatCuspIncomingEvaluation
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (hι : Function.Injective ι) (f : ℂ → S)
variable (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
variable (a : Cusps F ζ hζ C R P H U) (s : ℂ) (hs : s ∈ KPContActualChamberNormalSeries.V)

export KPContActualChamberCasimirJets.CuspAnalytic (actualCuspSheet_translation actualCuspSheet_kernel_representative actualCuspSheet_crossAction)

include hι hf hs

theorem actualCuspSheet_norm_crossAction
    (h : stabilizer F ζ hζ C R P H U a) (t : ℝ)
    (p : KPCuspCharts.Cross F) (ε : rootsOfUnity 3 F) :
    ‖KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t
      ((geometry F ζ hζ C R P H U a).crossAction h p).1
      ((geometry F ζ hζ C R P H U a).crossAction h p).2 ε‖ =
    ‖KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t p.1 p.2 ε‖ := by
  rw [KPContActualChamberCasimirJets.CuspAnalytic.actualCuspSheet_crossAction F ζ hζ C R P H U ι hι f hf a s hs,
    norm_mul, KPContSectorCoveredQuotientVocabulary.chi_norm, one_mul]

end DedekindZetaZeroFree.KPContinuation.ChamberModerateGrowth

end
