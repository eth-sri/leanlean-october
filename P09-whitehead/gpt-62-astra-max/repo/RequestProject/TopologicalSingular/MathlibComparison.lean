module

public import RequestProject.TopologicalSingular.SimplexCoordinates
public import RequestProject.Statement
public import RequestProject.TopologicalSingular.SingularChainHomotopy
public import RequestProject.TopologicalSingular.ContractibleSingularChains
public import RequestProject.FreeSingularChainComparison

@[expose] public section

noncomputable section

open scoped ContinuousMap

namespace FiniteChains.TopologicalSingular
open CategoryTheory AlgebraicTopology

variable (X : TopCat.{0})

/-- Removing the universe lift from singular simplices is a simplicial
isomorphism, not merely a degreewise bijection. -/
def simplicesMathlibIso :
    simplices X ≅ TopCat.toSSet.obj X :=
  NatIso.ofComponents (fun n => (((simplexCoordinates n.unop.len).symm.arrowCongr (Homeomorph.refl X)).toEquiv.trans
      (TopCat.toSSetObjEquiv X n).symm).toIso) (by
    intro n m a
    apply ConcreteCategory.hom_ext
    intro σ
    change Simplex X n.unop.len at σ
    apply (TopCat.toSSetObjEquiv X m).injective
    apply ContinuousMap.ext
    intro z
    exact congrArg σ (simplexCoordinates_map a.unop z).symm)

/-- The explicit integral chains agree with Mathlib's free singular chains. -/
def freeComplexMathlibIso :
    complex X ≅ AlternatingFaceMapComplex.obj (TopCat.toSSet.obj X ⋙ ModuleCat.free ℤ) :=
  (alternatingFaceMapComplex (ModuleCat.{0} ℤ)).mapIso
    (Functor.isoWhiskerRight (simplicesMathlibIso X) (ModuleCat.free ℤ))

theorem freeComplexMathlibIso_natural {X Y : TopCat.{0}} (f : X ⟶ Y) :
    chainMap f.hom ≫ (freeComplexMathlibIso Y).hom =
      (freeComplexMathlibIso X).hom ≫ AlternatingFaceMapComplex.map
        (Functor.whiskerRight (TopCat.toSSet.map f) (ModuleCat.free ℤ)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro σ r
  change Finsupp.mapDomain _ (Finsupp.mapDomain _ _) =
    Finsupp.mapDomain _ (Finsupp.mapDomain _ _)
  aesop

/-- The actual explicit singular chain complex computes the coefficients and
singular-homology functor occurring in `Whitehead.Acyclic`. -/
def complexMathlibIso (X : TopCat.{0}) :=
  freeComplexMathlibIso X ≪≫ FiniteChains.freeSingularChainComplexIso X

theorem complexMathlibIso_natural {X Y : TopCat.{0}} (f : X ⟶ Y) :
    chainMap f.hom ≫ (complexMathlibIso Y).hom =
      (complexMathlibIso X).hom ≫ ((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
        _).map f := by
  dsimp only [complexMathlibIso, Iso.trans_hom]
  rw [← Category.assoc, freeComplexMathlibIso_natural, Category.assoc,
    FiniteChains.freeSingularChainComplexIso_natural, Category.assoc]

def homologyMathlibIso (X : TopCat.{0}) (n : ℕ) :
    (complex X).homology n ≅ ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).obj X :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) _ n).mapIso
    (complexMathlibIso X)

theorem homologyMathlibIso_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    HomologicalComplex.homologyMap (chainMap f.hom) n ≫ (homologyMathlibIso Y n).hom =
      (homologyMathlibIso X n).hom ≫ ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        _).map f := by
  change (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) _ n).map _ ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) _ n).map _ =
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) _ n).map _ ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) _ n).map _
  grind [complexMathlibIso_natural]

/-- Homotopy equivalent spaces have isomorphic actual integral singular homology. -/
def mathlibHomologyIsoOfHomotopyEquiv {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (n : ℕ) :=
  (homologyMathlibIso (TopCat.of X) n).symm ≪≫ homologyIsoOfHomotopyEquiv e n ≪≫
    homologyMathlibIso (TopCat.of Y) n

end FiniteChains.TopologicalSingular

namespace Whitehead
open CategoryTheory

/-- Acyclicity in the original statement is invariant under homotopy equivalence. -/
theorem acyclic_iff_of_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) : Acyclic X ↔ Acyclic Y := by
  constructor
  · intro h n hn
    exact (h n hn).of_iso
      (FiniteChains.TopologicalSingular.mathlibHomologyIsoOfHomotopyEquiv e n).symm
  · intro h n hn
    exact (h n hn).of_iso
      (FiniteChains.TopologicalSingular.mathlibHomologyIsoOfHomotopyEquiv e n)

end Whitehead
