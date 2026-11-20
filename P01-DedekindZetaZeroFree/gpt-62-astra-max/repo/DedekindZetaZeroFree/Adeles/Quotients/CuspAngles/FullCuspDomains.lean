module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.Cusps.AngularShellLaw
public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.HighHoroballOverlap

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField Topology NNReal ENNReal
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsActualAngularDomainSource
open KPMsActualAngularSource KPMsActualCuspSource
open KPMsResidualTailRestoration.SharpConstantTerm
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
    {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
    (S : SourceRecipe F ζ hζ R P H) (U : KPMsActualAngularSource.Level F ζ hζ)

theorem continuous_archBasepoint :
    Continuous (KPMsFixedHaarDisintegration.archBasepoint F) := by apply @DedekindZetaZeroFree.KPMsFixedHaar.SphericalProjection.archBasepoint_continuous <;> assumption

theorem product_splitting :
    ∃ e : (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ*
      KPMsActualAngularSource.G F ζ hζ,
      ∀ a c, e (a,c) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val := by apply @DedekindZetaZeroFree.KPActualComponentHaarSources.actual_product_splitting <;> assumption

end DedekindZetaZeroFree.KPMsActualAngularDomainSource

end
