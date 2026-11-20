module

public import RequestProject.QCubeThreeGeometricKernel

@[expose] public section

/-! Exact coefficient coordinates for finite chains on the six actual facets of a three-cube. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

variable (c : QThreeCube A)

noncomputable def qThreeOrderedCoordinates :
    (QSquare A →₀ ℤ) →ₗ[ℤ] ((Fin 3 × ZMod 2) →₀ ℤ) :=
  Finsupp.lcomapDomain _ (qThreeFaceSquare_injective c)

/-- The six actual facet coefficients reconstruct every chain supported below the three-cube. -/
theorem qThreeOrderedCoordinates_reconstruct
    (r : QSquare A →₀ ℤ) (hr : ∀ s ∈ r.support, s.1 < c.1) :
    Finsupp.mapDomain (qThreeFaceSquare c) (qThreeOrderedCoordinates c r) = r := by
  apply Finsupp.mapDomain_comapDomain _ (qThreeFaceSquare_injective c)
  solve_by_elim [qThreeFaceSquare_exhaustive]

end FiniteChains.Davis
