import RequestProject.OrderNerveRealizationContraction
import RequestProject.OrderNerveRealizationStarSheets
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected


namespace FiniteChains.Comb
open CategoryTheory

/-- Closed vertex-star carriers are contractible in the actual CW topology. -/
theorem orderNerveRealization_closedStar_contractible {P} [PartialOrder P] v :
    ContractibleSpace (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v) :
      Set (orderNerveRealization P)) := by
  let a : orderNerveVertexStar P v := ⟨v, Or.inl le_rfl⟩
  letI := orderNerveRealization_contractible_of_comparable a (by aesop)
  exact (orderNerveRealizationSubtypeHomeomorph _).symm.contractibleSpace
