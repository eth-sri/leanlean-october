module
public import OAI.NumberTheory.DirichletL.Reflection.MemberBudget
public import OAI.NumberTheory.DirichletL.Reflection.TupleMembers
public import OAI.NumberTheory.DirichletL.Reflection.GlobalEnergy

set_option linter.privateModule false

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

end
end SevenEighths.InverseReflectedPhase

end OAI
