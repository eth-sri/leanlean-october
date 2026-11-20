module

public import Glennie.Native.Statements
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Eval

/-! Exact coefficient arithmetic for the two finite rank checks. The Jordan product
is evaluated before extending scalars, so neither certificate needs a table of
real-valued intermediate products. -/
@[expose] public section
namespace Glennie.Exact

abbrev O (R : Type*) [CommRing R] := Quaternion R × Quaternion R
abbrev A (R : Type*) [CommRing R] := R × R × R × O R × O R × O R

variable {R : Type*} [CommRing R]

def conj (x : O R) : O R := (star x.1, -x.2)
def mul (x y : O R) : O R :=
  (x.1 * y.1 - star y.2 * x.2, y.2 * x.1 + x.2 * star y.1)
def dot (x y : O R) := (mul x (conj y)).1.re

def prod (h : R) : A R → A R → A R
  | (a,b,c,u,v,w), (d,e,f,s,t,z) =>
    (a*d + dot u s + dot v t, b*e + dot u s + dot w z, c*f + dot v t + dot w z,
     h • ((a+b) • s + (d+e) • u + mul v (conj z) + mul t (conj w)),
     h • ((a+c) • t + (d+f) • v + mul u z + mul s w),
     h • ((b+c) • z + (e+f) • w + mul (conj u) t + mul (conj s) v))

variable (f : R →+* ℝ)

def mapQ (x : Quaternion R) : Quaternion ℝ := ⟨f x.re, f x.imI, f x.imJ, f x.imK⟩
def mapO (x : O R) : Octonion := (mapQ f x.1, mapQ f x.2)
def realize : A R → Albert
  | (a,b,c,u,v,w) => ⟨f a,f b,f c,mapO f u,mapO f v,mapO f w⟩

@[simp] theorem mapO_add (x y : O R) : mapO f (x+y) = mapO f x + mapO f y := by
  ext <;> simp [mapO, mapQ]
@[simp] theorem mapO_smul (c : R) (x : O R) : mapO f (c • x) = f c • mapO f x := by
  ext <;> simp [mapO, mapQ]
@[simp] theorem mapO_mul (x y : O R) : mapO f (mul x y) = octMul (mapO f x) (mapO f y) := by
  ext <;> simp [mapO, mapQ, mul, octMul, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul]
@[simp] theorem mapO_conj (x : O R) : mapO f (conj x) = octConj (mapO f x) := by
  ext <;> simp [mapQ, mapO, conj, octConj]
@[simp] theorem map_dot (x y : O R) : f (dot x y) = octDot (mapO f x) (mapO f y) :=
  congrArg octRe (by rw [mapO_mul, mapO_conj] : mapO f (mul x (conj y)) = _)

@[simp] theorem realize_prod (h : R) (hh : f h = 1/2) (x y : A R) :
    realize f (prod h x y) = jordan (realize f x) (realize f y) := by
  rcases x with ⟨a,b,c,u,v,w⟩; rcases y with ⟨d,e,g,s,t,z⟩
  apply Albert.ext <;> simp [realize, prod, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, hh]

@[simp] theorem realize_smul (r : R) (x : A R) : realize f (r • x) = f r • realize f x := by
  apply Albert.ext <;> simp [realize]
@[simp] theorem realize_add (x y : A R) : realize f (x + y) = realize f x + realize f y := by
  apply Albert.ext <;> simp [realize]
@[simp] theorem realize_sub (x y : A R) : realize f (x - y) = realize f x - realize f y := by
  ext <;> simp [realize, mapO, mapQ]
@[simp] theorem realize_zero : realize f 0 = 0 := by ext <;> simp [realize, mapO, mapQ]

def one : A R := (1,1,1,0,0,0)
def markX : A R := (-1,0,1,0,0,0)
def markY (i : R) : A R := (0,0,0,(1,0),(⟨0,i,0,0⟩,0),(1,0))
def markZ : A R := (0,0,0,(0,⟨0,0,1,0⟩),(0,-1),(-⟨0,0,0,1⟩,0))

local macro "marksimp" : tactic => `(tactic| ext <;> simp [realize, mapO, mapQ, one,
  markX, markY, markZ, witnessX, witnessY, witnessZ, octScalar, octI, octJL, octL, octK,
  quatI, quatJ, quatK])
@[simp] theorem realize_one : realize f one = 1 := by marksimp
@[simp] theorem realize_x : realize f markX = witnessX := by marksimp
@[simp] theorem realize_y : realize f (markY 1) = witnessY := by marksimp
@[simp] theorem realize_z : realize f markZ = witnessZ := by marksimp

def pairing (x y : A R) := x.1*y.1 + x.2.1*y.2.1 + x.2.2.1*y.2.2.1 +
  2*(dot x.2.2.2.1 y.2.2.2.1 + dot x.2.2.2.2.1 y.2.2.2.2.1 + dot x.2.2.2.2.2 y.2.2.2.2.2)
theorem cast_pairing (x y : A R) : f (pairing x y) = inner (realize f x) (realize f y) := by
  simp [pairing,inner_coordinates,realize,map_ofNat]

/-- Arrays give constant-time access during certificate production. -/
def pack {n : ℕ} (M : Matrix (Fin n) (Fin n) R) := Array.ofFn fun i => Array.ofFn (M i)
def unpack {n : ℕ} (a : Array (Array R)) : Matrix (Fin n) (Fin n) R :=
  fun i j => (a.getD i.val #[]).getD j.val 0

/-- Gauss-Jordan certificate producer. Correctness of the producer is not a
premise: in each use the kernel checks the proposed left inverse by multiplication. -/
def inverseCandidate {n : ℕ} [DecidableEq R] [Inhabited R] (inv : R → R)
    (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := Id.run do
  let mut a := Array.ofFn fun i => Array.ofFn (M i) ++ Array.ofFn ((1 : Matrix (Fin n) (Fin n) R) i)
  for k in [:n] do
    let p := (List.range n).find? fun i => k ≤ i ∧ (a[i]!)[k]! ≠ 0
    let some i := p | return 0
    a := a.swapIfInBounds k i
    let row := a[k]!.map (inv (a[k]!)[k]! * ·)
    a := a.mapIdx fun i r => if i == k then row else r.zipWith (fun x y => x - r[k]! * y) row
  return fun i j => (a[i.val]!)[n+j.val]!

theorem mapped_left_inverse {n : ℕ} {M B : Matrix (Fin n) (Fin n) R} (h : B * M = 1) :
    B.map f * M.map f = 1 := by
  simpa using congrArg (RingHom.mapMatrix f) h

end Glennie.Exact
