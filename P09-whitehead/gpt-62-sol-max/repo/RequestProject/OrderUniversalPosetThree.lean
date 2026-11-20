module

public import RequestProject.OrderUniversalPosetHom
public import RequestProject.FinsuppBasis
public import RequestProject.OrderUniversalThree

@[expose] public section

/-! The actual lifted three-boundary under the universal-cover order identification. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

noncomputable def uOrderTet (t : OrdTet (UOrder P a)) : UOrdTet P a :=
  ⟨(t.1.1, ordTetMap uOrderEnd uOrderEnd_monotone t), rfl⟩

/-- The four actual lifted faces have precisely the alternating nerve boundary. -/
theorem uOrderTet_boundary (t : OrdTet (UOrder P a)) :
    Finsupp.mapDomain uOrderFace (ordTetBoundary t) = uOrdTetBoundary (uOrderTet t) := by
  rw [ordTetBoundary, uOrdTetBoundary, mapDomain_tetrahedronBoundary]
  apply congrArg tetrahedronBoundary
  funext i
  fin_cases i
  · exact Subtype.ext (Prod.ext t.2.1.2.symm (Subtype.ext rfl))
  all_goals rfl

/-- The cellular comparison commutes with the full actual universal-cover three-boundary. -/
theorem uOrderHom_ordBoundary3 (c : OrdTet (UOrder P a) →₀ ℤ) :
    chain2 uOrderHom (ordBoundary3 c) = uOrdBoundary3 (Finsupp.mapDomain uOrderTet c) := by
  finsupp_basis c
  intro t
  rw [ordBoundary3, Finsupp.linearCombination_single, map_smul]
  change 1 • Finsupp.mapDomain uOrderFace (ordTetBoundary t) = _
  rw [uOrderTet_boundary, Finsupp.mapDomain_single, uOrdBoundary3,
    Finsupp.linearCombination_single]

end FiniteChains.Comb
