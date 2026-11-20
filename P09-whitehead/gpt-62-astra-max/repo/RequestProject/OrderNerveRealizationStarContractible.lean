module

public import RequestProject.OrderNerveRealizationContraction
public import RequestProject.OrderNerveRealizationStarSheets
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory

/-- Closed vertex-star carriers are contractible in the actual CW topology. -/
theorem orderNerveRealization_closedStar_contractible {P : Type} [PartialOrder P] (v : P) :
    ContractibleSpace (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v) :
      Set (orderNerveRealization P)) := by
  let a : orderNerveVertexStar P v := ⟨v, Or.inl le_rfl⟩
  letI := orderNerveRealization_contractible_of_comparable a (fun p => p.property)
  exact (orderNerveRealizationSubtypeHomeomorph (orderNerveVertexStar P v)).symm.contractibleSpace

end FiniteChains.Comb
