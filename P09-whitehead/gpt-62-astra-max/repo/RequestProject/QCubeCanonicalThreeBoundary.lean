module

public import RequestProject.QCubeThreeComponentRecovery

@[expose] public section

/-! The cubical boundary in dimension three. -/
noncomputable section
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

def qThreeCubicalBoundary : (QThreeCube A →₀ ℤ) →ₗ[ℤ] (QSquare A →₀ ℤ) :=
  Finsupp.linearCombination ℤ qThreeCubicalFaceBoundary

end FiniteChains.Davis
