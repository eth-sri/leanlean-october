import Mathlib.Tactic

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.SingularPrism
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.CategoryTheory.Whiskering

/-! # Continuous homotopies induce actual chain homotopies

The prism operator is packaged in Mathlib's `Homotopy`, on the singular
complex already defined in this project. Consequently homotopic maps have
equal maps on homology. No homology comparison or exactness is assumed.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular

open CategoryTheory AlgebraicTopology

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

  (f : C(X, Y))
noncomputable def simplicesMap  : simplices X ⟶ simplices Y where
  app n := TypeCat.ofHom (simplexMap f n.unop.len)
  naturality _ _ _ := rfl

noncomputable def chainMap  : complex X ⟶ complex Y :=
  AlternatingFaceMapComplex.map (Functor.whiskerRight (simplicesMap f) freeZ)

theorem chainMap_f  (n : ℕ) :
    (chainMap f).f n = ModuleCat.ofHom (map f n) := rfl

theorem chainMap_id : chainMap (ContinuousMap.id X) = 𝟙 (complex X) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  exact map_id n

theorem chainMap_comp (f : C(X, Y)) (g : C(Y, Z)) :
    chainMap (g.comp f) = chainMap f ≫ chainMap g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  exact map_comp f g n

variable {f g : C(X, Y)}
noncomputable def prismComponent  (H : ContinuousMap.Homotopy f g)
    (i j : ℕ) : (complex X).X i ⟶ (complex Y).X j :=
  if h : j = i + 1 then h ▸ ModuleCat.ofHom (SingularPrism.prism H i) else 0

theorem prismComponent_succ  (H : ContinuousMap.Homotopy f g) (i : ℕ) :
    prismComponent H i (i + 1) = ModuleCat.ofHom (SingularPrism.prism H i) := by
  simp [prismComponent]

noncomputable def chainHomotopy  (H : ContinuousMap.Homotopy f g) :
    _root_.Homotopy (chainMap g) (chainMap f) where
  hom := prismComponent H
  zero i j hij := by
    aesop (add simp [prismComponent])
  comm i := by
    cases i with
    | zero =>
      rw [_root_.Homotopy.dNext_zero_chainComplex, zero_add,
        _root_.Homotopy.prevD_chainComplex, prismComponent_succ, complex_d, chainMap_f, chainMap_f]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change map g 0 c = boundary 0 (SingularPrism.prism H 0 c) + map f 0 c
      rw [SingularPrism.prism_identity_zero]
      abel
    | succ i =>
      rw [_root_.Homotopy.dNext_succ_chainComplex, _root_.Homotopy.prevD_chainComplex,
        prismComponent_succ, prismComponent_succ, complex_d, complex_d, chainMap_f, chainMap_f]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change map g (i + 1) c = SingularPrism.prism H i (boundary i c) +
        boundary (i + 1) (SingularPrism.prism H (i + 1) c) + map f (i + 1) c
      have hh := SingularPrism.prism_identity_succ H i c
      rw [add_comm (SingularPrism.prism H i (boundary i c)), hh]
      abel

noncomputable def chainHomotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y) :
    _root_.HomotopyEquiv (complex X) (complex Y) where
  hom := chainMap e.toFun
  inv := chainMap e.invFun
  homotopyHomInvId := by
    rw [← chainMap_comp, ← chainMap_id]
    exact (chainHomotopy e.left_inv.some).symm
  homotopyInvHomId := by
    rw [← chainMap_comp, ← chainMap_id]
    exact (chainHomotopy e.right_inv.some).symm

noncomputable def homologyIsoOfHomotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ)  :=
  (chainHomotopyEquiv e).toHomologyIso n

end FiniteChains.TopologicalSingular
