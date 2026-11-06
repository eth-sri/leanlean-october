import RequestProject.FreeIntegerCoproduct
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
noncomputable section


namespace FiniteChains
open CategoryTheory

/-- Free integral chains on the actual singular simplicial set are naturally
isomorphic to the actual Mathlib singular chain complex with integral coefficients. -/
def freeSingularChainComplexIso X :
    AlgebraicTopology.AlternatingFaceMapComplex.obj (TopCat.toSSet.obj X ⋙ ModuleCat.free ℤ) ≅
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj X :=
  (AlgebraicTopology.alternatingFaceMapComplex _).mapIso
    (CategoryTheory.Functor.isoWhiskerLeft _ freeIntegerCoproductNatIso)

/-- Categorical homology of the free singular chains is genuine integral singular homology. -/
def freeSingularHomologyIso X n :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj
      (TopCat.toSSet.obj X ⋙ ModuleCat.free ℤ)).homology n ≅
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
          (ModuleCat.of ℤ ℤ)).obj X) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso
    (freeSingularChainComplexIso X)

/-- The coefficient identification commutes with every actual continuous map. -/
theorem freeSingularChainComplexIso_natural (f : X ⟶ Y) :
    AlgebraicTopology.AlternatingFaceMapComplex.map
        (Functor.whiskerRight (TopCat.toSSet.map f) (ModuleCat.free ℤ)) ≫
      (freeSingularChainComplexIso Y).hom =
    (freeSingularChainComplexIso X).hom ≫
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map f) := by
  change (AlgebraicTopology.alternatingFaceMapComplex _).map _ ≫
      (AlgebraicTopology.alternatingFaceMapComplex _).map _ =
    (AlgebraicTopology.alternatingFaceMapComplex _).map _ ≫
      (AlgebraicTopology.alternatingFaceMapComplex _).map _
  aesop

/-- Naturality of the identification with integral singular homology in every degree. -/
theorem freeSingularHomologyIso_natural (f : X ⟶ Y) n :
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map
      (AlgebraicTopology.AlternatingFaceMapComplex.map
        (Functor.whiskerRight (TopCat.toSSet.map f) (ModuleCat.free ℤ))) ≫
      (freeSingularHomologyIso Y n).hom =
    (freeSingularHomologyIso X n).hom ≫
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).map f) := by
  change (HomologicalComplex.homologyFunctor _ _ n).map _ ≫
      (HomologicalComplex.homologyFunctor _ _ n).map _ =
    (HomologicalComplex.homologyFunctor _ _ n).map _ ≫
      (HomologicalComplex.homologyFunctor _ _ n).map _
  grind [← Functor.map_comp, freeSingularChainComplexIso_natural]
