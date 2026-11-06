import RequestProject.OrderNerveRealizationComparison
import RequestProject.FreeSingularChainComparison
import RequestProject.MathlibOrderNerveComplexNaturality
import RequestProject.Tac
noncomputable section


bwd

namespace FiniteChains.Comb
open CategoryTheory

/-- The realization unit induces an actual map to Mathlib integral singular homology.
This definition makes no claim that the map is an isomorphism. -/
def orderNerveSingularH2Comparison P [PartialOrder P] :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).homology 2 ⟶
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)) :=
  orderNerveRealizationH2Comparison P ≫
    (FiniteChains.freeSingularHomologyIso _ 2).hom

/-- The actual singular-homology comparison is natural for monotone maps. -/
theorem orderNerveSingularH2Comparison_natural {P Q}
    [PartialOrder P] [PartialOrder Q] f hf :
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 2).map
      (mathlibOrderNerveChainMap f hf) ≫ orderNerveSingularH2Comparison Q =
    orderNerveSingularH2Comparison P ≫
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).map (orderNerveRealizationMap f hf)) := by
  unfold orderNerveSingularH2Comparison
  rw [← Category.assoc, orderNerveRealizationH2Comparison_natural, Category.assoc]
  change _ ≫ ((HomologicalComplex.homologyFunctor _ _ 2).map
      (AlgebraicTopology.AlternatingFaceMapComplex.map
        (Functor.whiskerRight (TopCat.toSSet.map (orderNerveRealizationMap f hf))
          _)) ≫ _) = _
  rw [FiniteChains.freeSingularHomologyIso_natural, Category.assoc]

/-- A zero order-homology pushdown annihilates all singular classes in the comparison image. -/
theorem orderNerveSingularH2Comparison_pushdown_zero {P Q}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) hf
    (hzero : orderNerveH2Map f hf = 0) :
    orderNerveSingularH2Comparison P ≫
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).map (orderNerveRealizationMap f hf)) = 0 := by
  rw [← orderNerveSingularH2Comparison_natural,
    mathlibOrderNerveComplex_homologyMap_zero f hf hzero]
  exact CategoryTheory.Limits.zero_comp

/-- The actual order-cell second-homology classes map to genuine singular classes. -/
def orderCellSingularH2Map P [PartialOrder P] :
    OrderNerveH2 P →ₗ[ℤ]
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)) :=
  (orderNerveSingularH2Comparison P).hom.comp
    (mathlibOrderNerveComplexH2Equiv P).toLinearMap

/-- Naturality of the comparison from actual order-cell classes to singular classes. -/
theorem orderCellSingularH2Map_natural {P Q} [PartialOrder P] [PartialOrder Q]
    f hf z :
    ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).map (orderNerveRealizationMap f hf)).hom
        (orderCellSingularH2Map P z)) = orderCellSingularH2Map Q (orderNerveH2Map f hf z) := by
  have h := congrArg (fun k =>
      k (mathlibOrderNerveComplexH2Equiv P z))
    (orderNerveSingularH2Comparison_natural f hf)
  change (orderNerveSingularH2Comparison Q).hom
      (((HomologicalComplex.homologyFunctor _ _ 2).map
        (mathlibOrderNerveChainMap f hf)).hom (mathlibOrderNerveComplexH2Equiv P z)) =
    ((((AlgebraicTopology.singularHomologyFunctor _ 2).obj
      (ModuleCat.of ℤ ℤ)).map (orderNerveRealizationMap f hf)).hom
        (orderCellSingularH2Map P z)) at h
  rw [mathlibOrderNerveComplexH2Equiv_natural] at h
  exact h.symm
