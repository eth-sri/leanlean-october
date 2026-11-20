module

public import DedekindZetaZeroFree.Metaplectic.Unipotent.RationalFrameConjugation

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField NNReal
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent
open KPMsClearedTruncationL2
open KPMsResidualTailRestoration.SharpConstantTerm.FiberStability
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
alias fullCusp_finiteSubgroup_eq := DedekindZetaZeroFree.KPActualComponentHaarSources.PartialRationalTiling.actual_finiteSubgroup_eq

theorem fullCusp_product_splitting :
    ∃ e : (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ* G F ζ hζ,
      ∀ a c, e (a,c) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val := by apply @DedekindZetaZeroFree.KPActualComponentHaarSources.actual_product_splitting <;> assumption
variable {F ζ hζ}
variable {C : ModelData F ζ hζ} {D : Iwasawa F ζ hζ}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
    {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
    {A : KPMsRationalCompactCrossPairing.RawCompactComparison F ζ hζ C D R P H}
    {U : Level F ζ hζ}

end DedekindZetaZeroFree.KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent

end
