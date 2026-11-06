module
public import OAI.NumberTheory.DirichletL.Reflection.ExtractedRow

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ ι : Type*} [Fintype φ] [Fintype ι] {N a c : Eis} {mode : Bool}

def extractedDualScale (D : Ideal Eis) (Y : ℝ) : ℝ := max 1 (Y/(Ideal.absNorm D:ℝ))

end
end SevenEighths.InverseReflectedPhase

end OAI
