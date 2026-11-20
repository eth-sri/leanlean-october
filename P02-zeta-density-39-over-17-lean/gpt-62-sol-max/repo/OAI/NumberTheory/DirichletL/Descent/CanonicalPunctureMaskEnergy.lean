module
public import OAI.NumberTheory.DirichletL.Descent.CanonicalPunctureMask

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve InverseInitialClippedColumns
local notation "Eis" => ActualEisensteinCubic.O

end SevenEighths.InverseMoment
end

end OAI
