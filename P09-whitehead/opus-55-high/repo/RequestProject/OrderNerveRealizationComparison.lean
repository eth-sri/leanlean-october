import RequestProject.MathlibOrderNerveNaturality
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Abelian
import RequestProject.Tac
noncomputable section


bwd

namespace FiniteChains.Comb
open CategoryTheory
variable (P : Type) [PartialOrder P]

/-- The actual Mathlib geometric realization of the actual poset nerve. -/
def orderNerveRealization := SSet.toTop.obj (nerve P)

/-- The canonical actual map from the poset nerve to the singular set of its realization. -/
def orderNerveRealizationUnit :
    nerve P ⟶ TopCat.toSSet.obj (orderNerveRealization P) :=
  sSetTopAdj.unit.app (nerve P)

/-- Free integral chains on the actual singular simplicial set of the realization. -/
def orderNerveRealizationSingularModule : SimplicialObject (ModuleCat ℤ) :=
  TopCat.toSSet.obj (orderNerveRealization P) ⋙ ModuleCat.free ℤ

/-- The actual realization-unit chain map into the free singular chains. -/
def orderNerveRealizationChainComparison :
    AlgebraicTopology.AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P) ⟶
      AlgebraicTopology.AlternatingFaceMapComplex.obj
        (orderNerveRealizationSingularModule P) :=
  AlgebraicTopology.AlternatingFaceMapComplex.map
    (CategoryTheory.Functor.whiskerRight (orderNerveRealizationUnit P) _)

/-- The canonical comparison on actual categorical second homology. -/
def orderNerveRealizationH2Comparison :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).homology 2 ⟶
      (AlgebraicTopology.AlternatingFaceMapComplex.obj
        (orderNerveRealizationSingularModule P)).homology 2 :=
  (HomologicalComplex.homologyFunctor _ _ 2).map
    (orderNerveRealizationChainComparison P)

variable {P} {Q : Type} [PartialOrder Q]

/-- The actual realized map induced by a monotone map of posets. -/
def orderNerveRealizationMap (f : P → Q) (hf : Monotone f) :
    orderNerveRealization P ⟶ orderNerveRealization Q :=
  SSet.toTop.map (nerveMap hf.functor)

/-- The canonical realization-unit comparison is natural under actual monotone maps. -/
theorem orderNerveRealizationUnit_natural f hf :
    nerveMap hf.functor ≫ orderNerveRealizationUnit Q =
      orderNerveRealizationUnit P ≫ TopCat.toSSet.map (orderNerveRealizationMap f hf) :=
  sSetTopAdj.unit.naturality _

/-- The actual chain map on the free singular chains induced by the realized map. -/
def orderNerveRealizationSingularChainMap (f : P → Q) (hf : Monotone f) :
    AlgebraicTopology.AlternatingFaceMapComplex.obj
      (orderNerveRealizationSingularModule P) ⟶
    AlgebraicTopology.AlternatingFaceMapComplex.obj
      (orderNerveRealizationSingularModule Q) :=
  AlgebraicTopology.AlternatingFaceMapComplex.map
    (CategoryTheory.Functor.whiskerRight
      (TopCat.toSSet.map (orderNerveRealizationMap f hf)) _)

/-- The actual realization comparison is natural on the actual chain complexes. -/
theorem orderNerveRealizationChainComparison_natural f hf :
    mathlibOrderNerveChainMap f hf ≫ orderNerveRealizationChainComparison Q =
      orderNerveRealizationChainComparison P ≫ orderNerveRealizationSingularChainMap f hf := by
  change (AlgebraicTopology.alternatingFaceMapComplex _).map _ ≫
      (AlgebraicTopology.alternatingFaceMapComplex _).map _ =
    (AlgebraicTopology.alternatingFaceMapComplex _).map _ ≫
      (AlgebraicTopology.alternatingFaceMapComplex _).map _
  simp [mathlibOrderNerveModuleMap, ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.whiskerRight_comp, orderNerveRealizationUnit_natural]

/-- Naturality also holds on actual categorical second homology. -/
theorem orderNerveRealizationH2Comparison_natural f hf :
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 2).map
        (mathlibOrderNerveChainMap f hf) ≫ orderNerveRealizationH2Comparison Q =
      orderNerveRealizationH2Comparison P ≫
        (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 2).map
          (orderNerveRealizationSingularChainMap f hf) := by
  change (HomologicalComplex.homologyFunctor _ _ 2).map _ ≫
      (HomologicalComplex.homologyFunctor _ _ 2).map _ =
    (HomologicalComplex.homologyFunctor _ _ 2).map _ ≫
      (HomologicalComplex.homologyFunctor _ _ 2).map _
  grind [← CategoryTheory.Functor.map_comp, orderNerveRealizationChainComparison_natural]
