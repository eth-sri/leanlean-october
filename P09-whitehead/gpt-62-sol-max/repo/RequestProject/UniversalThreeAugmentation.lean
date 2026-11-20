module

public import RequestProject.OrderUniversalThree
public import RequestProject.FinsuppBasis
public import RequestProject.CombPi2

@[expose] public section

/-! Forgetting the deck coordinate of the actual lifted three-boundary. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] (a : P)

theorem hurewicz_uOrdTetBoundary (t : UOrdTet P a) :
    hurewicz (orderCx P) a (uOrdTetBoundary t) = ordTetBoundary t.1.2 := by
  change Finsupp.mapDomain (univProj (orderCx P) a).onF (uOrdTetBoundary t) = _
  rw [uOrdTetBoundary, ordTetBoundary, mapDomain_tetrahedronBoundary]
  rfl

/-- Augmentation commutes with the actual degree-three cellular boundary. -/
theorem hurewicz_uOrdBoundary3 (c : UOrdTet P a →₀ ℤ) :
    hurewicz (orderCx P) a (uOrdBoundary3 c) =
      ordBoundary3 (Finsupp.mapDomain (fun t : UOrdTet P a => t.1.2) c) := by
  finsupp_basis c
  simp [uOrdBoundary3, Finsupp.linearCombination_single, hurewicz_uOrdTetBoundary, ordBoundary3]

end FiniteChains.Comb
