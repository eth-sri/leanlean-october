module
public import OAI.NumberTheory.DirichletL.Detector.GaussianDecomposition
public import OAI.NumberTheory.DirichletL.Detector.LowCompletion

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

end SevenEighths.ProbePhysical
end

end OAI
