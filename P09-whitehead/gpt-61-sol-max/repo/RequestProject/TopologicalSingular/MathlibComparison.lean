import Mathlib.Tactic

import RequestProject.TopologicalSingular.SimplexCoordinates
import RequestProject.Statement
import RequestProject.TopologicalSingular.SingularChainHomotopy
import RequestProject.TopologicalSingular.ContractibleSingularChains
import RequestProject.FreeSingularChainComparison

open scoped ContinuousMap

set_option backward.isDefEq.respectTransparency.types false

set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 40000
set_option maxHeartbeats 800000

namespace FiniteChains.TopologicalSingular
open CategoryTheory AlgebraicTopology

variable (X : TopCat.{0})
/-- Removing the universe lift from singular simplices is a simplicial
isomorphism, not merely a degreewise bijection. -/
noncomputable def simplicesMathlibIso  :
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
noncomputable def freeComplexMathlibIso (X : TopCat.{0}) :
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
  change Finsupp.mapDomain _ (Finsupp.mapDomain _ (Finsupp.single σ r)) =
    Finsupp.mapDomain _ (Finsupp.mapDomain _ (Finsupp.single σ r))
  simp only [Finsupp.mapDomain_single]
  rfl

/-- The actual explicit singular chain complex computes the coefficients and
singular-homology functor occurring in `Whitehead.Acyclic`. -/
noncomputable def complexMathlibIso   :=
  freeComplexMathlibIso X ≪≫ FiniteChains.freeSingularChainComplexIso X

theorem complexMathlibIso_natural {X Y : TopCat.{0}} (f : X ⟶ Y) :
    chainMap f.hom ≫ (complexMathlibIso Y).hom =
      (complexMathlibIso X).hom ≫ ((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map f := by
  dsimp only [complexMathlibIso, Iso.trans_hom]
  rw [← Category.assoc, freeComplexMathlibIso_natural, Category.assoc,
    FiniteChains.freeSingularChainComplexIso_natural, Category.assoc]

noncomputable def homologyMathlibIso  (n : ℕ)  :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).mapIso
    (complexMathlibIso X)

theorem homologyMathlibIso_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    HomologicalComplex.homologyMap (chainMap f.hom) n ≫ (homologyMathlibIso Y n).hom =
      (homologyMathlibIso X n).hom ≫ ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).map f := by
  change (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).map _ ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).map _ =
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).map _ ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).map _
  rw [← Functor.map_comp, ← Functor.map_comp, complexMathlibIso_natural]

/-- Homotopy equivalent spaces have isomorphic actual integral singular homology. -/
noncomputable def mathlibHomologyIsoOfHomotopyEquiv {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (n : ℕ)  :=
  (homologyMathlibIso (TopCat.of X) n).symm ≪≫ homologyIsoOfHomotopyEquiv e n ≪≫
    homologyMathlibIso (TopCat.of Y) n

end FiniteChains.TopologicalSingular

namespace Whitehead


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
