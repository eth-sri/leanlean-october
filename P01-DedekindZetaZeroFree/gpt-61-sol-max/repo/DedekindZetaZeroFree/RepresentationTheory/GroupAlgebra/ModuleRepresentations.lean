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





























end Semiring

section Character

variable {k G : Type*} [Field k] [Monoid G]









@[simp]
theorem _root_.Representation.char_ofModule'_asModule {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : _root_.Representation k G V) (g : G) :
    (_root_.Representation.ofModule' (k := k) (G := G) ρ.asModule).character g = ρ.character g := by
  have h : _root_.Representation.ofModule' (k := k) (G := G) ρ.asModule g =
      ρ.asModuleEquiv.symm.conj (ρ g) := by
    ext x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
      _root_.Representation.asModuleEquiv_symm_map_rho, LinearEquiv.symm_apply_apply,
      ofModule'_apply, MonoidAlgebra.of_apply]
  rw [_root_.Representation.character, h, LinearMap.trace_conj', _root_.Representation.character]

end Character

end Representation

end DedekindZetaZeroFree.TauCeti
