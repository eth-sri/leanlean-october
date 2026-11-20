module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.SingularPrism
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.CategoryTheory.Whiskering

@[expose] public section

/-! # Continuous homotopies induce actual chain homotopies

The prism operator is packaged in Mathlib's `Homotopy`, on the singular
complex already defined in this project. Consequently homotopic maps have
equal maps on homology. No homology comparison or exactness is assumed.
-/
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FiniteChains.TopologicalSingular

open CategoryTheory AlgebraicTopology

universe u
variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

variable (f : C(X, Y))

def simplicesMap : simplices X ⟶ simplices Y where
  app n := TypeCat.ofHom (simplexMap f n.unop.len)
  naturality _ _ _ := rfl

def chainMap : complex X ⟶ complex Y :=
  AlternatingFaceMapComplex.map (Functor.whiskerRight (simplicesMap f) freeZ)

theorem chainMap_f (n : ℕ) :
    (chainMap f).f n = ModuleCat.ofHom (map f n) := rfl

theorem chainMap_id : chainMap (ContinuousMap.id X) = 𝟙 (complex X) := by
  apply HomologicalComplex.Hom.ext
  funext n
  solve_by_elim [map_id]

theorem chainMap_comp (f : C(X, Y)) (g : C(Y, Z)) :
    chainMap (g.comp f) = chainMap f ≫ chainMap g := by
  apply HomologicalComplex.Hom.ext
  funext n
  solve_by_elim [map_comp]

def prismComponent {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)
    (i j : ℕ) : (complex X).X i ⟶ (complex Y).X j :=
  if h : j = i + 1 then h ▸ ModuleCat.ofHom (SingularPrism.prism H i) else 0

theorem prismComponent_succ {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (i : ℕ) :
    prismComponent H i _ = ModuleCat.ofHom (SingularPrism.prism H i) := by
  simp [prismComponent]

def chainHomotopy {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    _root_.Homotopy (chainMap g) (chainMap f) where
  hom := prismComponent H
  zero i j hij := by
    have hne : j ≠ i + 1 := by
      intro he
      simp_all
    simp_all [prismComponent, dif_neg]
  comm i := by
    cases i with
    | zero =>
      rw [_root_.Homotopy.dNext_zero_chainComplex, zero_add,
        _root_.Homotopy.prevD_chainComplex, prismComponent_succ, complex_d, chainMap_f, chainMap_f]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change map g 0 c = boundary 0 (SingularPrism.prism H 0 c) + map f 0 c
      simp [SingularPrism.prism_identity_zero]
    | succ i =>
      rw [_root_.Homotopy.dNext_succ_chainComplex, _root_.Homotopy.prevD_chainComplex,
        prismComponent_succ, prismComponent_succ, complex_d, complex_d, chainMap_f, chainMap_f]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change map g _ c = SingularPrism.prism H i (boundary i c) +
        boundary _ (SingularPrism.prism H _ c) + map f _ c
      rw [add_comm (SingularPrism.prism H i _), (SingularPrism.prism_identity_succ H i c)] <;> simp_all

variable (e : ContinuousMap.HomotopyEquiv X Y)

def chainHomotopyEquiv :
    _root_.HomotopyEquiv (complex X) (complex Y) where
  hom := chainMap e.toFun
  inv := chainMap e.invFun
  homotopyHomInvId := by
    rw [← chainMap_comp, ← chainMap_id]
    exact (chainHomotopy e.left_inv.some).symm
  homotopyInvHomId := by
    rw [← chainMap_comp, ← chainMap_id]
    exact (chainHomotopy e.right_inv.some).symm

def homologyIsoOfHomotopyEquiv (n : ℕ) :=
  (chainHomotopyEquiv e).toHomologyIso n

end FiniteChains.TopologicalSingular
