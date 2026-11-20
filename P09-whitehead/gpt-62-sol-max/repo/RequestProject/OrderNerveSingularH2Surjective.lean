module

public import RequestProject.OrderNervePositiveHomologyIso
public import RequestProject.OrderNerveSingularHomologyComparison

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular

theorem orderNerveSingularH2Comparison_factor (P : Type) [PartialOrder P] :
    orderNerveSingularH2Comparison P =
      HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) 2 ≫
        (homologyMathlibIso (orderNerveRealization P) 2).hom := by
  have he : orderNerveExplicitSingularMap P ≫ (complexMathlibIso (orderNerveRealization P)).hom =
      orderNerveRealizationChainComparison P ≫
        (FiniteChains.freeSingularChainComplexIso (orderNerveRealization P)).hom := by
    simp [orderNerveExplicitSingularMap, complexMathlibIso, Category.assoc]
  change (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 2).map
      (orderNerveRealizationChainComparison P) ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 2).map
        (FiniteChains.freeSingularChainComplexIso (orderNerveRealization P)).hom =
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 2).map
      (orderNerveExplicitSingularMap P) ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 2).map
        (complexMathlibIso (orderNerveRealization P)).hom
  erw [← Functor.map_comp, ← Functor.map_comp, he]

theorem orderNerveSingularH2Comparison_isIso (P : Type) [PartialOrder P] :
    IsIso (orderNerveSingularH2Comparison P) := by
  rw [orderNerveSingularH2Comparison_factor]
  letI := orderNerveExplicitSingularHomology_isIso P 1
  infer_instance

/-- A zero cellular pushdown annihilates every actual singular second-homology
class, without any remaining comparison-image hypothesis. -/
theorem orderNerveSingularH2Map_zero_of_orderH2Map_zero {P Q : Type}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) (hf : Monotone f)
    (hzero : orderNerveH2Map f hf = 0) :
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
      (orderNerveRealizationMap f hf)) = 0 := by
  letI := orderNerveSingularH2Comparison_isIso P
  apply (cancel_epi (orderNerveSingularH2Comparison P)).mp
  erw [orderNerveSingularH2Comparison_pushdown_zero f hf hzero, Limits.comp_zero]

end FiniteChains.Comb
