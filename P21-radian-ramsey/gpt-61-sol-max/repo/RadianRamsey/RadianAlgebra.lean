module

public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Theorem D, generic algebra: the radian 9-gon evaluation matrix has nonzero determinant

Theorem D of the spherical-ramsey note (`note/spherical-ramsey.tex`, doi:10.5281/zenodo.23396387;
exact check there: `certificates/radian_det.py`). Mirrors the
specialization argument of OpenAI's `NineGridDeterminant` / `NineRationalDeterminant` (openai/math @ fd4aeeb2, Apache-2.0),
for one parameter per tensor factor instead of nine.

With `t = tan (θ/2)`, `(1 + i t)^(2n) = A_n(t) + i B_n(t)` and
`(cos nθ, sin nθ) = (A_n(t), B_n(t)) / (1 + t²)^n`. `rot z n = (A_n(z), B_n(z))`.
Everything is stated over an arbitrary commutative ring and moved by ring homomorphisms.
The determinant of the denominator-cleared matrix is certified at `(T, U) = (2, 3)`
by transforming its reduction modulo 17 to a Vandermonde matrix (kernel `decide`).
-/

namespace OAI.EuclideanRamsey
noncomputable section
namespace Radian

section Generic

variable {R : Type*} [CommRing R]

/-- `rot z n = (A_n(z), B_n(z))`, the real and imaginary parts of `(1 + i z)^(2n)`. -/
def rot (z : R) : ℕ → R × R
  | 0 => (1, 0)
  | n + 1 => ((1 - z ^ 2) * (rot z n).1 - 2 * z * (rot z n).2,
      2 * z * (rot z n).1 + (1 - z ^ 2) * (rot z n).2)

/-- Denominator-cleared augmented coordinates of the `n`-th point. -/
def qv (z : R) (n : ℕ) : Fin 3 → R := ![(1 + z ^ 2) ^ n, (rot z n).1, (rot z n).2]

/-- Column labels: `j ↦ (j / 3, j % 3)`. -/
def col (j : Fin 9) : Fin 3 × Fin 3 := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin (3 * 3)).symm j

/-- The denominator-cleared `9 × 9` tensor evaluation matrix; column `j ↔ (j / 3, j % 3)`. -/
def Ecl (z w : R) : Matrix (Fin 9) (Fin 9) R := fun k j =>
  qv z k (col j).1 * qv w k (col j).2

variable {S : Type*} [CommRing S]

theorem map_rot (f : R →+* S) (z : R) (n : ℕ) :
    f (rot z n).1 = (rot (f z) n).1 ∧ f (rot z n).2 = (rot (f z) n).2 := by
  induction n <;> simp_all [rot, map_ofNat]

theorem map_Ecl (f : R →+* S) (z w : R) : f.mapMatrix (Ecl z w) = Ecl (f z) (f w) := by
  ext k j
  fin_cases j <;> simp [Ecl, col, finProdFinEquiv, Fin.divNat, Fin.modNat, qv, map_rot f z k, map_rot f w k]

end Generic

/-! ## The integer certificate at `(T, U) = (2, 3)` -/

/-- Over `𝔽₁₇`, the complex-coordinate change turns the specialized matrix into
an ordinary Vandermonde matrix on nine distinct elements. -/
theorem det_Ecl_int : (Ecl (2 : ℤ) 3).det ≠ 0 := by
  letI : Fact (Nat.Prime 17) := ⟨by decide⟩
  let A : Matrix (Fin 3) (Fin 3) (ZMod 17) := !![1,0,0;0,1,1;0,4,-4]
  let xs : Fin 9 → ZMod 17 := ![16,12,10,11,4,9,14,2,13]
  have he : Ecl (2 : ZMod 17) 3 * (show Matrix (Fin 9) (Fin 9) (ZMod 17) from
      fun i j => (A.kronecker A) (col i) (col j)) =
      (Matrix.vandermonde xs).transpose := by decide +kernel
  have hv := Matrix.det_vandermonde_ne_zero_iff.mpr (by decide +kernel : Function.Injective xs)
  rw [← Matrix.det_transpose, ← he, Matrix.det_mul] at hv
  intro h
  apply left_ne_zero_of_mul hv
  have h' := congrArg (Int.castRingHom (ZMod 17)) h
  simpa only [RingHom.map_det, map_Ecl, map_ofNat, map_zero] using h'

/-! ## Two independent variables -/

abbrev Poly := MvPolynomial (Unit ⊕ Unit) ℚ

def T : Poly := MvPolynomial.X (Sum.inl ())
def U : Poly := MvPolynomial.X (Sum.inr ())

theorem det_Ecl_poly : (Ecl T U).det ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval (Sum.elim (fun _ => (2:ℚ)) (fun _ => 3))) h
  rw [RingHom.map_det, map_Ecl] at he
  apply det_Ecl_int
  apply (Int.cast_injective (α := ℚ))
  change (Int.castRingHom ℚ) (Ecl (2 : ℤ) 3).det = 0
  rw [RingHom.map_det, map_Ecl]
  simpa only [T, U, MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr,
    map_zero, map_ofNat] using he

/-! ## The actual (uncleared) evaluation matrix in a faithful field realization -/


variable {K : Type*} [Field K]

/-- Augmented coordinates `(1, cos nθ, sin nθ)` as rational functions of `z = tan (θ/2)`. -/
def rv (z : K) (n : ℕ) : Fin 3 → K :=
  ![1, (rot z n).1 / (1 + z ^ 2) ^ n, (rot z n).2 / (1 + z ^ 2) ^ n]

/-- The tensor evaluation matrix with rows `k` and columns `(j / 3, j % 3)`. -/
def G (z w : K) : Matrix (Fin 9) (Fin 9) K := fun k j =>
  rv z k (col j).1 * rv w k (col j).2

theorem clear_rv (z : K) (hz : 1 + z ^ 2 ≠ 0) (n : ℕ) (a : Fin 3) :
    (1 + z ^ 2) ^ n * rv z n a = qv z n a := by
  fin_cases a <;> simp [rv, qv] <;> field_simp

theorem Ecl_eq (z w : K) (hz : 1 + z ^ 2 ≠ 0) (hw : 1 + w ^ 2 ≠ 0) :
    Ecl z w = Matrix.diagonal (fun k : Fin 9 => (1 + z ^ 2) ^ (k : ℕ) * (1 + w ^ 2) ^ (k : ℕ)) *
      G z w := by
  ext k j
  rw [Matrix.diagonal_mul]
  simp [Ecl, G, ← clear_rv z hz, ← clear_rv w hw]
  ring

theorem det_G_ne_zero (φ : Poly →+* K) (hφ : Function.Injective φ) :
    (G (φ T) (φ U)).det ≠ 0 := by
  have hden v : 1 + φ (MvPolynomial.X v) ^ 2 ≠ 0 := by
    intro hz
    have h : (1 + MvPolynomial.X v ^ 2 : Poly) = 0 := hφ (by simpa using hz)
    have := congrArg MvPolynomial.constantCoeff h
    norm_num at this
  intro h
  apply det_Ecl_poly
  apply hφ
  rw [map_zero,RingHom.map_det,map_Ecl,
    Ecl_eq (φ T) (φ U) (hden (Sum.inl ())) (hden (Sum.inr ())),Matrix.det_mul,h,mul_zero]


end Radian
end

end OAI.EuclideanRamsey
