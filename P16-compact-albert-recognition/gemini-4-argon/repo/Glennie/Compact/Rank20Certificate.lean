module

public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Glennie.Compact.Rank20Certificate

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

abbrev Z3 := Zsqrtd 3

/-- 72 times the flat-base derivative matrix, entry ⟨a, b⟩ = a + b sqrt3. -/
def JZ : Matrix (Fin 20) (Fin 20) Z3 :=
  !![⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨-2, 0⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨-2, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨0, 2⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 2⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, 0⟩, ⟨0, 2⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨0, -2⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨-2, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-2, 0⟩, ⟨0, 2⟩;
     ⟨0, -4⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩;
     ⟨0, -4⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩;
     ⟨0, -4⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨0, 2⟩;
     ⟨0, 0⟩, ⟨8, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, 0⟩, ⟨0, 2⟩;
     ⟨0, 0⟩, ⟨8, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨8, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩;
     ⟨0, 4⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩;
     ⟨0, 4⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-2, 0⟩, ⟨0, 2⟩;
     ⟨0, 4⟩, ⟨4, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 4⟩, ⟨4, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨4, 0⟩, ⟨-2, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨-8, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨-8, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨4, 0⟩, ⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]

/-- The ring hom Z3 -> ZMod 65521 sending sqrt3 to 627. -/
def phiP : Z3 →+* ZMod 65521 := Zsqrtd.lift ⟨627, by decide +kernel⟩

/-- The row permutation of the pivoted elimination (seven swaps). -/
def rowPerm : Equiv.Perm (Fin 20) :=
  Equiv.swap 0 8 *
    Equiv.swap 1 11 *
    Equiv.swap 6 8 *
    Equiv.swap 7 8 *
    Equiv.swap 8 9 *
    Equiv.swap 9 10 *
    Equiv.swap 18 19

/-- Unit lower-triangular factor (mod p). -/
def Lp : Matrix (Fin 20) (Fin 20) (ZMod 65521) :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 65519, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 65519, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 65519, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 65520, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 65520, 65520, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 65520, 0, 43681, 21841, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 65520, 21841, 43681, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 65520, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 1, 65520, 0, 65520, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 65520, 0, 43681, 21841, 65520, 65520, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 65520, 21841, 43681, 0, 65520, 2, 1, 1, 1, 0, 0, 0, 0, 0, 0;
     65520, 65520, 0, 0, 1, 1, 65520, 65520, 0, 0, 0, 0, 65520, 0, 1, 0, 0, 0, 0, 0;
     65520, 65520, 0, 0, 0, 1, 43680, 21840, 0, 1, 65519, 65520, 65520, 65520, 32760, 1, 0, 0, 0, 0;
     65520, 0, 65520, 0, 0, 1, 65520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
     65520, 0, 65520, 0, 0, 1, 21840, 43681, 65520, 0, 65520, 65520, 0, 0, 0, 0, 65520, 1, 0, 0;
     0, 65520, 2, 65520, 0, 0, 21840, 43680, 1, 1, 0, 0, 65520, 0, 0, 0, 0, 65520, 1, 0;
     0, 65520, 2, 65520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65520, 1, 0, 1]

/-- Upper-triangular factor (mod p). -/
def Up : Matrix (Fin 20) (Fin 20) (ZMod 65521) :=
  !![63013, 65517, 0, 0, 2, 64267, 0, 0, 65517, 0, 2, 0, 0, 0, 2, 1254, 64894, 1, 4, 0;
     0, 8, 0, 0, 2, 64267, 0, 0, 2, 64267, 65520, 627, 0, 0, 2, 64267, 627, 1, 65519, 1254;
     0, 0, 2, 1254, 65519, 64267, 0, 2, 0, 0, 1, 64894, 64267, 2, 0, 0, 0, 65519, 65519, 1254;
     0, 0, 0, 2508, 65515, 64267, 64894, 3, 0, 0, 3, 63640, 64267, 6, 0, 0, 627, 65518, 65515, 3762;
     0, 0, 0, 0, 6, 64267, 627, 3, 0, 0, 65518, 627, 64267, 65515, 0, 0, 64894, 65518, 6, 64267;
     0, 0, 0, 0, 0, 63013, 1254, 0, 0, 0, 0, 1254, 63013, 0, 0, 0, 64267, 0, 0, 63013;
     0, 0, 0, 0, 0, 0, 1881, 65518, 0, 0, 65518, 1881, 0, 0, 0, 0, 63640, 3, 6, 61759;
     0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65515, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 6, 1254, 65516, 64894, 64267, 65515, 0, 63013, 1254, 0, 65519, 64267;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 63013, 4, 1254, 64267, 6, 65515, 1254, 64894, 65518, 65513, 2508;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 63640, 0, 0, 0, 0, 0, 0, 65515, 3762;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3762, 0, 0, 0, 0, 0, 0, 0, 57997;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61759, 65515, 65509, 0, 0, 65515, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 6, 3762, 63640, 3, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65509, 0, 0, 65515, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3762, 63640, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64267, 2, 8, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 63013;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 63013;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5016]

/-- The LU certificate, checked by kernel evaluation on finite ZMod data. -/
theorem lu_certificate : (JZ.map phiP).submatrix rowPerm id = Lp * Up := by
  decide +kernel

theorem Up_upper : Up.IsUpperTriangular := by
  have hb : (List.finRange 20).all (fun i => (List.finRange 20).all
      (fun j => decide (j < i → Up i j = 0))) = true := by
    decide +kernel
  intro i j hij
  have h1 := List.all_eq_true.mp hb i (List.mem_finRange i)
  exact of_decide_eq_true (List.all_eq_true.mp h1 j (List.mem_finRange j)) hij

theorem Lp_lower : Lp.IsLowerTriangular := by
  have hb : (List.finRange 20).all (fun i => (List.finRange 20).all
      (fun j => decide (i < j → Lp i j = 0))) = true := by
    decide +kernel
  intro i j hij
  have h1 := List.all_eq_true.mp hb i (List.mem_finRange i)
  exact of_decide_eq_true (List.all_eq_true.mp h1 j (List.mem_finRange j))
    (OrderDual.toDual_lt_toDual.mp hij)

theorem det_Lp : Lp.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular Lp Lp_lower]
  decide +kernel

theorem det_Up : Up.det = 33121 := by
  rw [Matrix.det_of_isUpperTriangular Up_upper]
  decide +kernel

theorem sign_rowPerm : Equiv.Perm.sign rowPerm = -1 := by
  rw [rowPerm, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul]
  rw [Equiv.Perm.sign_swap (show (0 : Fin 20) ≠ 8 by decide),
    Equiv.Perm.sign_swap (show (1 : Fin 20) ≠ 11 by decide),
    Equiv.Perm.sign_swap (show (6 : Fin 20) ≠ 8 by decide),
    Equiv.Perm.sign_swap (show (7 : Fin 20) ≠ 8 by decide),
    Equiv.Perm.sign_swap (show (8 : Fin 20) ≠ 9 by decide),
    Equiv.Perm.sign_swap (show (9 : Fin 20) ≠ 10 by decide),
    Equiv.Perm.sign_swap (show (18 : Fin 20) ≠ 19 by decide)]
  decide +kernel

/-- phiP (det JZ) = det (72 J) mod p. -/
theorem phiP_det_JZ : phiP JZ.det = 32400 := by
  have h1 := Matrix.det_permute rowPerm (JZ.map phiP)
  rw [lu_certificate, Matrix.det_mul, det_Lp, det_Up, sign_rowPerm] at h1
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one] at h1
  have hD : (JZ.map phiP).det = -33121 := by linear_combination h1
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hD]
  decide +kernel

theorem det_JZ_ne_zero : JZ.det ≠ 0 := fun h => by
  have h2 := phiP_det_JZ; rw [h, map_zero] at h2; exact absurd h2 (by decide +kernel)

/-- The ring hom Z3 -> R sending sqrt3 to Real.sqrt 3. -/
def liftR : Z3 →+* ℝ := Zsqrtd.lift ⟨Real.sqrt 3, by norm_num⟩

theorem liftR_injective : Function.Injective liftR :=
  Zsqrtd.lift_injective _ fun n heq => by
    rcases (by omega : n ≤ -2 ∨ n = -1 ∨ n = 0 ∨ n = 1 ∨ 2 ≤ n) with h | rfl | rfl | rfl | h <;>
      nlinarith

/-- The real flat-base matrix J. -/
def JQ : Matrix (Fin 20) (Fin 20) ℝ :=
  Matrix.of fun r n => (((JZ r n).re : ℝ) + ((JZ r n).im : ℝ) * Real.sqrt 3) / 72

theorem JQ_eq : JQ = (72 : ℝ)⁻¹ • JZ.map liftR := by
  ext r n
  simp only [JQ, Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, liftR,
    Zsqrtd.lift_apply_apply, smul_eq_mul]
  ring

/-- The real 20x20 minor is nonsingular. -/
theorem det_JQ_ne_zero : JQ.det ≠ 0 := by
  rw [JQ_eq, Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) fun h =>
    det_JZ_ne_zero (liftR_injective (h.trans (map_zero liftR).symm))

end
end Glennie.Compact.Rank20Certificate
