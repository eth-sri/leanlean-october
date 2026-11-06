module
import Batteries.Tactic.Alias
import OAI.NumberTheory.DirichletL.PrimeRows.CubePrimeBound

public import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorMoments
public import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorExponent

@[expose] public section

namespace OAI

section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]

variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
alias nonfloorPoolOutside := _root_.OAI.SevenEighths.ProbeHighRowFamily.poolOutside

end SevenEighths.ProbeHighRowFamily

end

end OAI
