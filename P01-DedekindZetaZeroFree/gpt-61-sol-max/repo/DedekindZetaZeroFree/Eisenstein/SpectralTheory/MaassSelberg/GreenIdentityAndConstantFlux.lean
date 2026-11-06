module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Casimir.NormalPrincipalCoefficient

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal Topology BigOperators
open MeasureTheory

namespace DedekindZetaZeroFree.KPMsGreenConstantFlux

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev K := NumberField.InfinitePlace F → KPCplxPrincipalSeriesCharts.compactSubgroup

instance : MeasurableSpace (K F) := borel _
instance : BorelSpace (K F) := ⟨rfl⟩

section Atlas
variable {F ζ hζ} {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}


end Atlas
end DedekindZetaZeroFree.KPMsGreenConstantFlux

namespace DedekindZetaZeroFree

end DedekindZetaZeroFree

end
