module
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Rat.Defs
@[expose] public section
namespace Glennie.MatrixCertificate

/-- Gauss–Jordan elimination on an augmented matrix. Its output is only a
proposal: the product certificate below is checked by the kernel. -/
def inverseCandidateRows {R : Type*} [CommRing R] [DecidableEq R] [Inhabited R]
    {n : Nat} (inv : R → R) (A : Matrix (Fin n) (Fin n) R) : Array (Array R) :=
  Id.run do
    let mut a := Array.ofFn fun i : Fin n => Array.ofFn (A i) ++
      Array.ofFn fun j : Fin n => if i = j then 1 else 0
    for k in List.finRange n do
      if let some p := (List.finRange n).find? (fun i => k ≤ i && (a[i.val]!)[k.val]! != 0) then
        a := a.swapIfInBounds k p
        let row := a[k.val]!.map (inv ((a[k.val]!)[k.val]!) * ·)
        a := a.mapIdx fun i r =>
          if i = k then row else r.mapIdx fun j x => x - r[k.val]! * row[j]!
    return a.map (·.extract n (2*n))

def ofRows {R : Type*} [Inhabited R] {n : Nat} (rows : Array (Array R)) :
    Matrix (Fin n) (Fin n) R := fun i j => (rows[i.val]!)[j.val]!

theorem eq_of_check {R : Type*} [CommRing R] [DecidableEq R] {n : Nat}
    (A B : Matrix (Fin n) (Fin n) R)
    (h : (List.finRange n).all (fun i => (List.finRange n).all fun j =>
      decide (A i j = B i j)) = true) : A = B := by aesop

theorem det_ne_zero_of_inverse {R : Type*} [CommRing R] [Nontrivial R] {n : Nat}
    {A B : Matrix (Fin n) (Fin n) R} (h : A * B = 1) : A.det ≠ 0 := by exact?

end Glennie.MatrixCertificate
