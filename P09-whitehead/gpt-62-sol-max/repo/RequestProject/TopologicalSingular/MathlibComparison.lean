module

public import RequestProject.TopologicalSingular.SimplexCoordinates
public import RequestProject.Statement
public import RequestProject.TopologicalSingular.SingularChainHomotopy
public import RequestProject.TopologicalSingular.ContractibleSingularChains
public import RequestProject.FreeSingularChainComparison
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

@[expose] public section

open scoped ContinuousMap



namespace FiniteChains.TopologicalSingular
open CategoryTheory AlgebraicTopology

/-- Removing the universe lift from singular simplices is a simplicial
isomorphism, not merely a degreewise bijection. -/
noncomputable def simplicesMathlibIso (X : TopCat.{0}) :
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
    change σ (stdSimplex.map a.unop (simplexCoordinates m.unop.len z)) =
      σ (simplexCoordinates n.unop.len (Convexity.StdSimplex.map a.unop z))
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
noncomputable def complexMathlibIso (X : TopCat.{0}) :
    complex X ≅ ((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj X :=
  freeComplexMathlibIso X ≪≫ FiniteChains.freeSingularChainComplexIso X

theorem complexMathlibIso_natural {X Y : TopCat.{0}} (f : X ⟶ Y) :
    chainMap f.hom ≫ (complexMathlibIso Y).hom =
      (complexMathlibIso X).hom ≫ ((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map f := by
  dsimp only [complexMathlibIso, Iso.trans_hom]
  rw [← Category.assoc, freeComplexMathlibIso_natural, Category.assoc,
    FiniteChains.freeSingularChainComplexIso_natural, Category.assoc]

noncomputable def homologyMathlibIso (X : TopCat.{0}) (n : ℕ) :
    (complex X).homology n ≅ ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).obj X :=
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

end FiniteChains.TopologicalSingular

namespace Whitehead
open CategoryTheory AlgebraicTopology Limits

private theorem acyclic_of_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (h : Acyclic Y) : Acyclic X := by
  intro n hn
  let R := ModuleCat.of ℤ ℤ
  let F := (singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj R
  let f  := TopCat.ofHom e.toFun
  let g  := TopCat.ofHom e.invFun
  have H : TopCat.Homotopy (f ≫ g) (𝟙 _) := e.left_inv.some
  have eq : F.map (f ≫ g) = F.map (𝟙 _) := H.congr_homologyMap_singularChainComplexFunctor R n
  apply (IsZero.iff_id_eq_zero _).2
  change 𝟙 (F.obj (TopCat.of X)) = 0
  rw [← F.map_id, ← eq, F.map_comp, (h n hn).eq_of_tgt (F.map f) 0, zero_comp]

/-- Acyclicity is invariant under homotopy equivalence. -/
theorem acyclic_iff_of_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) : Acyclic X ↔ Acyclic Y :=
  ⟨acyclic_of_homotopyEquiv e.symm, acyclic_of_homotopyEquiv e⟩

end Whitehead
