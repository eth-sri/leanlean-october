module
public import OAI.NumberTheory.DirichletL.PrimeRows.FirstProduct
public import OAI.NumberTheory.DirichletL.Detector.HighRowsFirstHolomorphic

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CompletedGauss
local notation "O" => HeckeFamily.O

end SevenEighths.ProbeHighRowFamily

end

end OAI
