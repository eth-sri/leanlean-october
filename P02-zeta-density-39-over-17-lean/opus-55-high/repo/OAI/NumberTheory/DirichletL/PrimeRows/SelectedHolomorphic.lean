module
public import OAI.NumberTheory.DirichletL.PrimeRows.SelectedAnalytic

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => HeckeFamily.O

end SevenEighths.ProbeHighRowFamily

end

end OAI
