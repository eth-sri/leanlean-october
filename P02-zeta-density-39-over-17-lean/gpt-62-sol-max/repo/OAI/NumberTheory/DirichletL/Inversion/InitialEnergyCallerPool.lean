module
public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerSelector

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge IdealMobiusDivisorSum UniqueFactorizationMonoid SevenEighths.InverseInitialOverlap SevenEighths.InverseInitialRayAttachment SevenEighths.InverseInitialEnergyCallerSelector
namespace SevenEighths.InverseInitialEnergyCallerPool
local notation "Eis" => ActualEisensteinCubic.O

end SevenEighths.InverseInitialEnergyCallerPool

end

end OAI
