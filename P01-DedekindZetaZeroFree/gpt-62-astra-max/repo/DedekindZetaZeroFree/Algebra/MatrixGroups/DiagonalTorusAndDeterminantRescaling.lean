module

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

variable {k : Type u} {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

section Semiring

variable [Semiring k]

def diagGL : (ι → kˣ) →* GL ι k :=
  (Units.map (Matrix.diagonalRingHom ι k).toMonoidHom).comp
    (MulEquiv.piUnits).symm.toMonoidHom

@[simp]
theorem diagGL_coe (t : ι → kˣ) :
    (diagGL t : Matrix ι ι k) = Matrix.diagonal fun i => (t i : k) := rfl

theorem isUnit_apply_of_isDiag {g : GL ι k} (hg : (g : Matrix ι ι k).IsDiag) (i : ι) :
    IsUnit ((g : Matrix ι ι k) i i) := by
  have h₁ := congrFun (congrFun g.mul_inv i) i
  have h₂ := congrFun (congrFun g.inv_mul i) i
  rw [← hg.diagonal_diag, Matrix.diagonal_mul, Matrix.one_apply_eq] at h₁
  rw [← hg.diagonal_diag, Matrix.mul_diagonal, Matrix.one_apply_eq] at h₂
  exact ⟨⟨_, _, h₁, h₂⟩, rfl⟩

def diagonalTorus (k : Type u) [Semiring k] (n : ℕ) : Subgroup (GL (Fin n) k) :=
  MonoidHom.range (diagGL (k := k) (ι := Fin n))

@[simp]
theorem mem_diagonalTorus_iff {g : GL (Fin n) k} :
    g ∈ diagonalTorus k n ↔ (g : Matrix (Fin n) (Fin n) k).IsDiag := by
  refine ⟨?_, fun hg => ⟨fun i => (isUnit_apply_of_isDiag hg i).unit, Units.ext ?_⟩⟩
  · rintro ⟨t, rfl⟩
    exact Matrix.isDiag_diagonal _
  · exact hg.diagonal_diag

end Semiring

section CommSemiring

variable [CommSemiring k]

instance instIsMulCommutativeDiagonalTorus : IsMulCommutative (diagonalTorus k n) :=
  Subgroup.range_isMulCommutative _

section Scalar

end Scalar

end CommSemiring

variable [CommRing k]

end DedekindZetaZeroFree.TauCeti
