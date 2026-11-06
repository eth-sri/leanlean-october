module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightInvariantDifferentialWords
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.NativeLieWordReindexing
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GreenIdentity.PairingsAndFluxDefinitions

set_option linter.privateModule false

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open Filter
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingLocality
open KPContActualSphericalRightFieldIdentification
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
local notation "G" => KPSmoothLocalQuotientCharts.ActualCover F ζ hζ

open KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource

end DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingLocality

end
