module

public import OAI.NumberTheory.DirichletL.Reflection.CanonicalEnergy
public import OAI.NumberTheory.DirichletL.Reflection.DyadCompletionEnergy

set_option linter.privateModule false

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment


universe v
variable {Nlevel : ActualEisensteinCubic.O}


end SevenEighths.InverseReflectedPhase

end OAI
