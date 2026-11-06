module

public import OAI.NumberTheory.DirichletL.Reflection.ActualBounds
public import OAI.NumberTheory.DirichletL.Reflection.FamilyFactorization
public import OAI.NumberTheory.DirichletL.Descent.Sharp

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
noncomputable section
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : ActualEisensteinCubic.O} {mode : Bool}

def actualRowPhaseExtension (F : PrimeFamily φ) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (K : Ideal ActualEisensteinCubic.O) : ℂ :=
  if hK : Admissible K then actualRowPhase F K hK jF s u m else 0

end
end SevenEighths.InverseReflectedPhase

end OAI
