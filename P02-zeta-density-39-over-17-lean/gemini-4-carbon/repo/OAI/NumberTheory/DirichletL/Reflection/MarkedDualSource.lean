module
public import OAI.NumberTheory.DirichletL.Reflection.MarkedRestriction


@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
open scoped Classical BigOperators ContDiff
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
namespace PrimeFamily
variable {ι : Type*} [Fintype ι] (P : PrimeFamily ι)

end PrimeFamily
end
end SevenEighths.InverseReflectedPhase

end OAI
