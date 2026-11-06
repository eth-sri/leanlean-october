module

public import Mathlib

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Algebra.Group.Pi.Units
public import DedekindZetaZeroFree.Algebra.Matrices.DiagonalCentralizer

@[expose] public section


/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/Diagonal/Basic.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: import/module surface and TauCeti-owned namespace references only;
root Mathlib extensions are retained. Proof bodies otherwise unchanged.
License: vendor root LICENSE.
-/

open Matrix

universe u

namespace DedekindZetaZeroFree.TauCeti

variable {k : Type u}  {ι : Type*} [Fintype ι] [DecidableEq ι]

section Semiring

variable [Semiring k]

def diagGL : (ι → kˣ) →* GL ι k :=
  (Units.map (Matrix.diagonalRingHom ι k).toMonoidHom).comp
    (MulEquiv.piUnits).symm.toMonoidHom

@[simp]
theorem diagGL_coe (t : ι → kˣ) :
    (diagGL t : Matrix ι ι k) = Matrix.diagonal fun i => (t i : k) := rfl

































end Semiring

section CommSemiring

variable [CommSemiring k]




section Scalar











end Scalar

end CommSemiring

variable [CommRing k]















end DedekindZetaZeroFree.TauCeti
