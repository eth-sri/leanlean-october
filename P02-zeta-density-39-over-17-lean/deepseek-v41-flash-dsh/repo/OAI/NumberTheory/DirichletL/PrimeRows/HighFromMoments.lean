module
public import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorCollected
public import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorTransport

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.ProbeHighRowFamily

end

end OAI
