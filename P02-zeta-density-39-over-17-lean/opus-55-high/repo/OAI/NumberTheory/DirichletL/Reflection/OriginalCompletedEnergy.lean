module
public import OAI.NumberTheory.DirichletL.Reflection.CompletedRowsEnergy
public import OAI.NumberTheory.DirichletL.Reflection.PunctureLists

set_option linter.privateModule false

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

end
end SevenEighths.InverseReflectedPhase

end OAI
