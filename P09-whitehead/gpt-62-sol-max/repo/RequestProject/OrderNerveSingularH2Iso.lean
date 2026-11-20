module

public import RequestProject.OrderNerveSingularH2Surjective

@[expose] public section


namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular

/-- An actual isomorphism, with the original natural comparison as forward map. -/
noncomputable def orderCellSingularH2Equiv (P : Type) [PartialOrder P] :
    OrderNerveH2 P ≃ₗ[ℤ]
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
        (orderNerveRealization P)) := by
  letI := orderNerveSingularH2Comparison_isIso P
  exact (mathlibOrderNerveComplexH2Equiv P).trans
    (asIso (orderNerveSingularH2Comparison P)).toLinearEquiv

theorem orderCellSingularH2Equiv_natural {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) (z : OrderNerveH2 P) :
    ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
      (orderNerveRealizationMap f hf)).hom (orderCellSingularH2Equiv P z)) =
        orderCellSingularH2Equiv Q (orderNerveH2Map f hf z) :=
  orderCellSingularH2Map_natural f hf z

end FiniteChains.Comb
