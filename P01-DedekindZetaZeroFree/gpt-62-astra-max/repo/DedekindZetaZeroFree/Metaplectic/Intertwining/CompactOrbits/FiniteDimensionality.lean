module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.HarishChandraHeckeCore.FiniteDimensionalCompactOrbits

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Classical NumberField ENNReal NNReal Topology BigOperators
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualKernel.ScatteringResidue
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {T : KPMsRationalCompactCrossPairing.ModelData F ζ hζ}
    {D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
    {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
    (A : KPMsRationalCompactCrossPairing.RawCompactComparison F ζ hζ T D R P H)

variable {S : Submodule ℂ (KPMsFixedHaarDisintegration.X F ζ hζ → ℂ)}

alias source_raw_compact_orbit_finiteDimensional_public := SourceCoreCompactOrbit.source_finiteDimensional

end DedekindZetaZeroFree.KPGlobalResidualKernel.ScatteringResidue

end
