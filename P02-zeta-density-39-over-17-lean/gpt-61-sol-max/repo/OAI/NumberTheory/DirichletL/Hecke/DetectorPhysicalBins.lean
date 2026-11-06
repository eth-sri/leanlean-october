module
public import OAI.NumberTheory.DirichletL.Hecke.DetectorPrimeFamily
public import OAI.NumberTheory.DirichletL.Hecke.PrimeAmplitudeActual

@[expose] public section

namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace SevenEighths.HeckeDetectorPhysicalBins
open HeckeFamily HeckeDetectorPrimeFamily HeckePrimeAmplitudeBins
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.HeckeDetectorPhysicalBins

end

end OAI
