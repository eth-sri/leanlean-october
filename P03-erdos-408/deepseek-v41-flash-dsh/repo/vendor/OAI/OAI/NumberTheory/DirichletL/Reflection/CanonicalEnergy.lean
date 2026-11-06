module

public import OAI.NumberTheory.DirichletL.Reflection.MemberGeometry
public import OAI.NumberTheory.DirichletL.Reflection.CanonicalParameters
public import OAI.NumberTheory.DirichletL.Reflection.OriginalCellBounds

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
