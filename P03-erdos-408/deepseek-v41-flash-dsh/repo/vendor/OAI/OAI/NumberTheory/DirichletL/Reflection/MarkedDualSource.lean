module

public import OAI.NumberTheory.DirichletL.Reflection.MarkedRestriction

set_option linter.privateModule false

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
namespace PrimeFamily
variable {ι : Type*} [Fintype ι] (P : PrimeFamily ι)

end PrimeFamily
end
end SevenEighths.InverseReflectedPhase

end OAI
