module

public import Mathlib.RepresentationTheory.Character
public import DedekindZetaZeroFree.Algebra.LinearAlgebra.ProductTrace

/-
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/OfModule.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
-/

@[expose] public section

namespace DedekindZetaZeroFree.TauCeti

namespace Representation

open scoped MonoidAlgebra

section Semiring

variable {k G : Type*} [CommSemiring k] [Monoid G]

variable (M : Type*) [AddCommMonoid M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]

@[simp]
theorem ofModule'_apply (g : G) (x : M) :
    _root_.Representation.ofModule' (k := k) (G := G) M g x = MonoidAlgebra.single g (1 : k) • x :=
  rfl

theorem asAlgebraHom_ofModule' :
    (_root_.Representation.ofModule' (k := k) (G := G) M).asAlgebraHom = Algebra.lsmul k k M := by
  apply Equiv.apply_symm_apply

@[simp]
theorem asAlgebraHom_ofModule'_apply (r : k[G]) (x : M) :
    (_root_.Representation.ofModule' (k := k) (G := G) M).asAlgebraHom r x = r • x := by
  rw [asAlgebraHom_ofModule']
  rfl

noncomputable def ofModule'AsModuleEquiv :
    (_root_.Representation.ofModule' (k := k) (G := G) M).asModule ≃ₗ[k[G]] M where
  toFun := (_root_.Representation.ofModule' (k := k) (G := G) M).asModuleEquiv
  invFun := (_root_.Representation.ofModule' (k := k) (G := G) M).asModuleEquiv.symm
  map_add' := map_add _
  map_smul' r x := by
    rw [RingHom.id_apply, _root_.Representation.asModuleEquiv_map_smul,
      asAlgebraHom_ofModule'_apply]
  left_inv := (_root_.Representation.ofModule' (k := k) (G := G) M).asModuleEquiv.left_inv
  right_inv := (_root_.Representation.ofModule' (k := k) (G := G) M).asModuleEquiv.right_inv

@[simp]
theorem ofModule'AsModuleEquiv_apply
    (x : (_root_.Representation.ofModule' (k := k) (G := G) M).asModule) :
    ofModule'AsModuleEquiv M x = x :=
  (rfl)

end Semiring

section Character

variable {k G : Type*} [Field k] [Monoid G]

end Character

end Representation

end DedekindZetaZeroFree.TauCeti
