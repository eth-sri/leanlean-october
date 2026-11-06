module
public import OAI.NumberTheory.DirichletL.Detector.LowSlotMarks
public import OAI.NumberTheory.DirichletL.Detector.LowSlotWeights
public import OAI.NumberTheory.DirichletL.Reflection.Canonical

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

end SevenEighths.ProbePhysical
end

end OAI
