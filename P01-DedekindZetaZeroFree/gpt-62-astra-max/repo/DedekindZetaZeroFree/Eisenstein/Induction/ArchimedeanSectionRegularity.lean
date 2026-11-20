module

public import DedekindZetaZeroFree.Eisenstein.Continuation.SmoothSections.CoherentSpatialSeries
public import DedekindZetaZeroFree.Eisenstein.Residues.Automorphy.ArchimedeanSmoothness

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology ContDiff
namespace DedekindZetaZeroFree.EisensteinSmoothGerms.SmoothSource
open KPContActualSphericalRightFieldIdentification KPContActualCutoffPlusClearedGerm

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets (rightWord_continuous_of_chart_smooth)

theorem finite_level_arch_continuous
    (V : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : KPLiteralRaw.G F ζ hζ → ℂ)
    (hf : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => f (g * KPGlobalResidualConstruction.archChart F ζ hζ x))
      (KPGlobalResidualConstruction.archDomain F))
    (hl : ∀ g a, a ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ V → f (g * a) = f g) :
    Continuous f := by
  exact rightWord_continuous_of_chart_smooth F ζ hζ V f hf
    (fun g a => hl g a.val a.property) []
end DedekindZetaZeroFree.EisensteinSmoothGerms.SmoothSource

end
