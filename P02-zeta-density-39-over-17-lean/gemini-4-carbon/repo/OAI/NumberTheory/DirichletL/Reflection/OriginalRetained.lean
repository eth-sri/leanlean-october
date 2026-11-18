module
public import OAI.NumberTheory.DirichletL.Reflection.OriginalSector
public import OAI.NumberTheory.DirichletL.Reflection.InactiveEnergy


@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
open scoped Classical BigOperators ContDiff
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

end
end SevenEighths.InverseReflectedPhase

end OAI
