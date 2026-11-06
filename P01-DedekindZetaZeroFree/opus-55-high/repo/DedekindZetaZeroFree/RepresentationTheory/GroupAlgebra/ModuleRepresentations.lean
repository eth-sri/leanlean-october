module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Block

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
