module

public import RequestProject.MathlibOrderNerveNaturality
public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian

@[expose] public section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FiniteChains.Comb
open CategoryTheory
variable (P : Type) [PartialOrder P]

/-- The actual Mathlib geometric realization of the actual poset nerve. -/
def orderNerveRealization := SSet.toTop.obj (nerve P)

/-- The canonical actual map from the poset nerve to the singular set of its realization. -/
def orderNerveRealizationUnit :
    nerve P ⟶ TopCat.toSSet.obj (orderNerveRealization P) :=
  sSetTopAdj.unit.app _

/-- Free integral chains on the actual singular simplicial set of the realization. -/
def orderNerveRealizationSingularModule :=
  TopCat.toSSet.obj (orderNerveRealization P) ⋙ ModuleCat.free ℤ

/-- The actual realization-unit chain map into the free singular chains. -/
def orderNerveRealizationChainComparison :
    AlgebraicTopology.AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P) ⟶
      AlgebraicTopology.AlternatingFaceMapComplex.obj
        (orderNerveRealizationSingularModule P) :=
  AlgebraicTopology.AlternatingFaceMapComplex.map
    (CategoryTheory.Functor.whiskerRight (orderNerveRealizationUnit P) (ModuleCat.free ℤ))

/-- The canonical comparison on actual categorical second homology. -/
def orderNerveRealizationH2Comparison :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).homology 2 ⟶
      (AlgebraicTopology.AlternatingFaceMapComplex.obj
        (orderNerveRealizationSingularModule P)).homology 2 :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) _ 2).map
    (orderNerveRealizationChainComparison P)

variable {P} {Q : Type} [PartialOrder Q]

variable (f : P → Q) (hf : Monotone f)

/-- The actual realized map induced by a monotone map of posets. -/
def orderNerveRealizationMap :
    orderNerveRealization P ⟶ orderNerveRealization Q :=
  SSet.toTop.map (nerveMap hf.functor)

/-- The canonical realization-unit comparison is natural under actual monotone maps. -/
theorem orderNerveRealizationUnit_natural :
    nerveMap hf.functor ≫ orderNerveRealizationUnit Q =
      orderNerveRealizationUnit P ≫ TopCat.toSSet.map (orderNerveRealizationMap f hf) :=
  by apply sSetTopAdj.unit.naturality

/-- The actual chain map on the free singular chains induced by the realized map. -/
def orderNerveRealizationSingularChainMap :
    AlgebraicTopology.AlternatingFaceMapComplex.obj
      (orderNerveRealizationSingularModule P) ⟶
    AlgebraicTopology.AlternatingFaceMapComplex.obj
      (orderNerveRealizationSingularModule Q) :=
  AlgebraicTopology.AlternatingFaceMapComplex.map
    (CategoryTheory.Functor.whiskerRight
      (TopCat.toSSet.map (orderNerveRealizationMap f hf)) (ModuleCat.free ℤ))

/-- The actual realization comparison is natural on the actual chain complexes. -/
theorem orderNerveRealizationChainComparison_natural :
    mathlibOrderNerveChainMap f hf ≫ orderNerveRealizationChainComparison Q =
      orderNerveRealizationChainComparison P ≫ orderNerveRealizationSingularChainMap f hf := by
  change (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat ℤ)).map _ ≫
      (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat ℤ)).map _ =
    (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat ℤ)).map _ ≫
      (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat ℤ)).map _
  dsimp only [mathlibOrderNerveModuleMap]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.whiskerRight_comp,
    ← CategoryTheory.Functor.whiskerRight_comp, orderNerveRealizationUnit_natural]

/-- Naturality also holds on actual categorical second homology. -/
theorem orderNerveRealizationH2Comparison_natural :
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) _ 2).map
        (mathlibOrderNerveChainMap f hf) ≫ orderNerveRealizationH2Comparison Q =
      orderNerveRealizationH2Comparison P ≫
        (HomologicalComplex.homologyFunctor (ModuleCat ℤ) _ 2).map
          (orderNerveRealizationSingularChainMap f hf) := by
  change (HomologicalComplex.homologyFunctor (ModuleCat ℤ) _ 2).map _ ≫
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) _ 2).map _ =
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) _ 2).map _ ≫
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) _ 2).map _
  grind [orderNerveRealizationChainComparison_natural]

end FiniteChains.Comb
