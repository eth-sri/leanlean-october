module
public import Glennie.Native.Statements
public import AlbertGeometry.NativeOperatorTrace
@[expose] public section
namespace Glennie.ExactCoordinates
open scoped Quaternion

deriving instance DecidableEq for QuaternionAlgebra

abbrev Oct (R : Type*) [CommRing R] := Quaternion R × Quaternion R

/-- The polynomial coordinates of a Hermitian matrix over a coefficient ring.
The half in the Jordan product is an explicit coefficient. -/
structure Coords (R : Type*) [CommRing R] where
  d0 : R
  d1 : R
  d2 : R
  o01 : Oct R
  o02 : Oct R
  o12 : Oct R
  deriving DecidableEq

variable {R : Type*} [CommRing R]

@[simps!] instance cOne : One (Coords R) := ⟨⟨1, 1, 1, 0, 0, 0⟩⟩
@[simps!] instance cAdd : Add (Coords R) := ⟨fun x y =>
  ⟨x.d0 + y.d0, x.d1 + y.d1, x.d2 + y.d2, x.o01 + y.o01, x.o02 + y.o02, x.o12 + y.o12⟩⟩
@[simps!] instance cSub : Sub (Coords R) := ⟨fun x y =>
  ⟨x.d0 - y.d0, x.d1 - y.d1, x.d2 - y.d2, x.o01 - y.o01, x.o02 - y.o02, x.o12 - y.o12⟩⟩
@[simps!] instance cSMul : SMul R (Coords R) := ⟨fun a x =>
  ⟨a * x.d0, a * x.d1, a * x.d2, a • x.o01, a • x.o02, a • x.o12⟩⟩

def mulOct (x y : Oct R) : Oct R :=
  (x.1 * y.1 - star y.2 * x.2, y.2 * x.1 + x.2 * star y.1)
def conjOct (x : Oct R) : Oct R := (star x.1, -x.2)
def dot (x y : Oct R) : R :=
  x.1.re*y.1.re + x.1.imI*y.1.imI + x.1.imJ*y.1.imJ + x.1.imK*y.1.imK +
    x.2.re*y.2.re + x.2.imI*y.2.imI + x.2.imJ*y.2.imJ + x.2.imK*y.2.imK

def product (h : R) (x y : Coords R) : Coords R :=
  ⟨2*h*(x.d0*y.d0 + dot x.o01 y.o01 + dot x.o02 y.o02),
   2*h*(x.d1*y.d1 + dot x.o01 y.o01 + dot x.o12 y.o12),
   2*h*(x.d2*y.d2 + dot x.o02 y.o02 + dot x.o12 y.o12),
   h • ((x.d0+x.d1) • y.o01 + (y.d0+y.d1) • x.o01 +
     mulOct x.o02 (conjOct y.o12) + mulOct y.o02 (conjOct x.o12)),
   h • ((x.d0+x.d2) • y.o02 + (y.d0+y.d2) • x.o02 +
     mulOct x.o01 y.o12 + mulOct y.o01 x.o12),
   h • ((x.d1+x.d2) • y.o12 + (y.d1+y.d2) • x.o12 +
     mulOct (conjOct x.o01) y.o02 + mulOct (conjOct y.o01) x.o02)⟩

abbrev doubled := product (1 : R)

def tr (x : Coords R) := x.d0 + x.d1 + x.d2

/-- Row-major scalar ordering, after the three diagonal coordinates. -/
def slots : Fin 27 ≃ AlbertGeometry.NativeOperatorTrace.FullIndex :=
  (@finSumFinEquiv 3 24).symm.trans (Equiv.sumCongr (.refl (Fin 3)) (@finProdFinEquiv 3 8).symm)

def flattened : Albert ≃ₗ[ℝ] (Fin 27 → ℝ) :=
  AlbertGeometry.NativeOperatorTrace.fullCoordinates.trans (LinearEquiv.funCongrLeft ℝ ℝ slots)

def coords (x : Coords R) (i : Fin 27) : R :=
  match slots i with
  | .inl j => ![x.d0, x.d1, x.d2] j
  | .inr (j,k) =>
    AlbertGeometry.NativeOperatorTrace.octCoeff (![x.o01,x.o02,x.o12] j) k

def marks (R : Type*) [CommRing R] : Fin 3 → Coords R :=
  ![⟨-1,0,1,0,0,0⟩,
    ⟨0,0,0,(1,0),(⟨0,1,0,0⟩,0),(1,0)⟩,
    ⟨0,0,0,(0,⟨0,0,1,0⟩),(0,-1),(⟨0,0,0,-1⟩,0)⟩]

section Naturality
variable {S : Type*} [CommRing S] (f : R →+* S)

def rq (x : Quaternion R) : Quaternion S := ⟨f x.re, f x.imI, f x.imJ, f x.imK⟩
def ro (x : Oct R) : Oct S := (rq f x.1, rq f x.2)
def coeffMap (x : Coords R) : Coords S :=
  ⟨f x.d0, f x.d1, f x.d2, ro f x.o01, ro f x.o02, ro f x.o12⟩

attribute [local ext] Coords
macro "coord_map" : tactic => `(tactic|
  ext <;> simp [coeffMap, rq, ro, product, tr, dot, mulOct, conjOct, smul_eq_mul,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul])

@[simp] theorem coeffMap_one : coeffMap f 1 = 1 := by coord_map
@[simp] theorem coeffMap_add (x y : Coords R) : coeffMap f (x + y) = coeffMap f x + coeffMap f y := by coord_map
@[simp] theorem coeffMap_sub (x y : Coords R) : coeffMap f (x - y) = coeffMap f x - coeffMap f y := by coord_map
@[simp] theorem coeffMap_smul (r : R) (x : Coords R) :
    coeffMap f (r • x) = (f r) • coeffMap f x := by coord_map
@[simp] theorem ro_mul (x y : Oct R) : ro f (mulOct x y) = mulOct (ro f x) (ro f y) := by coord_map
@[simp] theorem ro_conj (x : Oct R) : ro f (conjOct x) = conjOct (ro f x) := by coord_map
@[simp] private theorem ro_add (x y : Oct R) : ro f (x+y) = ro f x + ro f y := by coord_map
@[simp] theorem ro_smul (r : R) (x : Oct R) : ro f (r • x) = f r • ro f x := by coord_map
@[simp] private theorem ro_dot (x y : Oct R) : f (dot x y) = dot (ro f x) (ro f y) := by
  simp [dot, ro, rq]

@[simp] theorem coeffMap_product (h : R) (x y : Coords R) :
    coeffMap f (product h x y) = product (f h) (coeffMap f x) (coeffMap f y) := by
  apply Coords.ext <;> simp [coeffMap, product, map_ofNat]
theorem map_tr (x : Coords R) : f (tr x) = tr (coeffMap f x) := by
  simp [tr, coeffMap]
end Naturality

variable (f : R →+* ℝ)

def realize (x : Coords R) : Albert :=
  ⟨f x.d0, f x.d1, f x.d2, ro f x.o01, ro f x.o02, ro f x.o12⟩

theorem realize_coeffMap (x : Coords R) :
    realize (RingHom.id ℝ) (coeffMap f x) = realize f x := rfl

@[simp] theorem realize_one : realize f 1 = 1 := by ext <;> simp [realize, ro, rq]
@[simp] theorem realize_add (x y : Coords R) : realize f (x+y) = realize f x + realize f y := by
  ext <;> simp [realize, ro, rq]
@[simp] theorem realize_sub (x y : Coords R) : realize f (x-y) = realize f x - realize f y := by
  ext <;> simp [realize, ro, rq]
@[simp] theorem realize_smul (r : R) (x : Coords R) : realize f (r • x) = (f r) • realize f x := by
  ext <;> simp [realize, ro, rq, smul_eq_mul]

private theorem real_dot (x y : Oct ℝ) : dot x y = octDot x y := by
  rw [octDot_coordinates]
  rfl

theorem realize_product_scaled (h : R) (x y : Coords R) :
    realize f (product h x y) = (2 * f h) • jordan (realize f x) (realize f y) := by
  apply Albert.ext <;> simp only [realize, product, map_add, map_mul, map_ofNat, ro_dot, real_dot,
    ro_smul, ro_add, ro_mul, ro_conj, jordan_coord, Albert.smul_d0, Albert.smul_d1, Albert.smul_d2,
    Albert.smul_o01, Albert.smul_o02, Albert.smul_o12, smul_smul]
  all_goals rw [show (2 * f h) * (1/2) = f h by ring] <;> rfl

@[simp] theorem realize_product (h : R) (hh : f h = 1/2) (x y : Coords R) :
    realize f (product h x y) = jordan (realize f x) (realize f y) := by
  rw [realize_product_scaled, hh]
  norm_num

@[simp] theorem realize_doubled (x y : Coords R) :
    realize f (doubled x y) = (2 : ℝ) • jordan (realize f x) (realize f y) := by
  simpa using realize_product_scaled f 1 x y

@[simp] theorem realize_tr (x : Coords R) : f (tr x) = trace (realize f x) := by
  simp [tr, trace, realize]

@[simp] theorem realize_marks (i : Fin 3) :
    realize f (marks R i) = SubmissionR03.nativeMarks i := by
  fin_cases i <;> ext <;> norm_num [marks, realize, ro, rq, SubmissionR03.nativeMarks, witnessX, witnessY, witnessZ,
    octScalar, octI, octJL, octK, octL, quatI, quatJ, quatK]

@[simp] theorem flattened_realize (x : Coords R) (i : Fin 27) :
    flattened (realize f x) i = f (coords x i) := by
  fin_cases i <;> rfl

end Glennie.ExactCoordinates
