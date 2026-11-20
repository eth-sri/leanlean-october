module

public import RequestProject.FreeIntegerCoproduct
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian

@[expose] public section

namespace FiniteChains
open CategoryTheory

variable (X : TopCat)

/-- Free integral chains on the actual singular simplicial set are naturally
isomorphic to the actual Mathlib singular chain complex with integral coefficients. -/
noncomputable def freeSingularChainComplexIso :
    AlgebraicTopology.AlternatingFaceMapComplex.obj (TopCat.toSSet.obj X ⋙ ModuleCat.free ℤ) ≅
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj X :=
  (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat ℤ)).mapIso
    (CategoryTheory.Functor.isoWhiskerLeft (TopCat.toSSet.obj X) freeIntegerCoproductNatIso)

/-- Categorical homology of the free singular chains is genuine integral singular homology. -/
noncomputable def freeSingularHomologyIso (n : ℕ) :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj
      (TopCat.toSSet.obj X ⋙ ModuleCat.free ℤ)).homology n ≅
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
          (ModuleCat.of ℤ ℤ)).obj X) :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) _ n).mapIso
    (freeSingularChainComplexIso X)

variable {X Y : TopCat} (f : X ⟶ Y)

/-- The coefficient identification commutes with every actual continuous map. -/
theorem freeSingularChainComplexIso_natural :
    AlgebraicTopology.AlternatingFaceMapComplex.map
        (Functor.whiskerRight (TopCat.toSSet.map f) (ModuleCat.free ℤ)) ≫
      (freeSingularChainComplexIso Y).hom =
    (freeSingularChainComplexIso X).hom ≫
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        _).map f) := by
  change (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat ℤ)).map _ ≫
      (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat ℤ)).map _ =
    (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat ℤ)).map _ ≫
      (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat ℤ)).map _
  aesop

/-- Naturality of the identification with integral singular homology in every degree. -/
theorem freeSingularHomologyIso_natural (n : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) _ n).map
      (AlgebraicTopology.AlternatingFaceMapComplex.map
        (Functor.whiskerRight (TopCat.toSSet.map f) (ModuleCat.free ℤ))) ≫
      (freeSingularHomologyIso Y n).hom =
    (freeSingularHomologyIso X n).hom ≫
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
        _).map f) := by
  change (HomologicalComplex.homologyFunctor (ModuleCat ℤ) _ n).map _ ≫
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) _ n).map _ =
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) _ n).map _ ≫
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) _ n).map _
  grind [freeSingularChainComplexIso_natural]

end FiniteChains
