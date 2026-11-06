module
public import OAI.NumberTheory.DirichletL.Descent.CanonicalLongWeight
public import OAI.NumberTheory.DirichletL.Descent.CanonicalLongCount
public import OAI.NumberTheory.DirichletL.Descent.CanonicalLongIntegral

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers InverseInitialClippedColumns IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

end SevenEighths.InverseMoment

end

end OAI
