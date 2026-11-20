module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.SingularPrism
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.CategoryTheory.Whiskering

@[expose] public section

/-! The chain map induced by a continuous map on the explicit singular complex. -/

namespace FiniteChains.TopologicalSingular

open CategoryTheory AlgebraicTopology

universe u
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def simplicesMap (f : C(X, Y)) : simplices X ⟶ simplices Y where
  app n := TypeCat.ofHom (simplexMap f n.unop.len)
  naturality _ _ _ := rfl

noncomputable def chainMap (f : C(X, Y)) : complex X ⟶ complex Y :=
  AlternatingFaceMapComplex.map (Functor.whiskerRight (simplicesMap f) freeZ)

end FiniteChains.TopologicalSingular
