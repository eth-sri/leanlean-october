module

public import OAI.NumberTheory.DirichletL.Reflection.ExtractedRow

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section

variable {φ ι : Type*} [Fintype φ] [Fintype ι] {N a c : ActualEisensteinCubic.O} {mode : Bool}

def extractedDualScale (D : Ideal ActualEisensteinCubic.O) (Y : ℝ)  := max 1 (Y/(Ideal.absNorm D:ℝ))

end
end SevenEighths.InverseReflectedPhase

end OAI
