module

public import OAI.NumberTheory.DirichletL.Descent.CanonicalLongNormalization

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers InverseInitialClippedColumns
local notation "O"=>ActualEisensteinCubic.O

end SevenEighths.InverseMoment

end

end OAI
