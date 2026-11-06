module
public import OAI.NumberTheory.DirichletL.Reflection.ActualBounds
public import OAI.NumberTheory.DirichletL.Reflection.FamilyFactorization
public import OAI.NumberTheory.DirichletL.Descent.Sharp

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
noncomputable section
open scoped EisensteinEis
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def actualRowPhaseExtension (F : PrimeFamily φ) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (u : Eisˣ) (m : ℕ) (K : Ideal Eis) : ℂ :=
  if hK : Admissible K then actualRowPhase F K hK jF s u m else 0





