module
public import OAI.NumberTheory.DirichletL.Reflection.DyadicTail
public import OAI.NumberTheory.DirichletL.Inversion.KernelSourceUniform


@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
open scoped Classical BigOperators ContDiff SchwartzMap
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

end
end SevenEighths.InverseReflectedPhase

end OAI
