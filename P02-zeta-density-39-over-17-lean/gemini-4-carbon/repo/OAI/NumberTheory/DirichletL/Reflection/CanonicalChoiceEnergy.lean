module
public import OAI.NumberTheory.DirichletL.Reflection.CanonicalDyads
public import OAI.NumberTheory.DirichletL.Reflection.DyadBudget
public import OAI.NumberTheory.DirichletL.Reflection.MemberChoiceTransport


@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
open scoped Classical BigOperators ContDiff
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

end
end SevenEighths.InverseReflectedPhase

end OAI
