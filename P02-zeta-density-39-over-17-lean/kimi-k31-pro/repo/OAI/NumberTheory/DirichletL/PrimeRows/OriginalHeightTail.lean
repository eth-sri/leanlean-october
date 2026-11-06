module
public import OAI.NumberTheory.DirichletL.PrimeRows.TailIntegral
public import OAI.NumberTheory.DirichletL.PrimeRows.FirstTransport

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

end SevenEighths.ProbeHighRowFamily

end

end OAI
