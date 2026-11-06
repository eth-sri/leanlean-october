/- The exact 20x20 matrix and its
determinant certificate, with the statement ring fixed as
  R6 = Z[1/6, theta]/(theta^2 - 3) = AdjoinRoot (X^2 - 3) over Localization.Away 6.
  * `JZ` is 72 J with entries in Z3 = Z[sqrt3] (literal). The real matrix is
    `JQ r n = (re + im sqrt3) / 72`; the R6 matrix is `JR = 72^-1 . iota(JZ)`.
  * Modulo p = 65521 with sqrt3 -> 627 (a ring hom Z3 -> ZMod p; no field
    hom Q(sqrt3) -> F_p is used): a row-pivoted LU factorization
    (seven explicit swaps, unit lower L, upper U) is checked by kernel `decide`
    on finite ZMod data, giving phiP (det JZ) = 32400.
  * Hence det JZ /= 0 in Z3; through the injective liftR (sqrt3 -> Real.sqrt 3),
    det JQ /= 0 over R; over R6, det JR /= 0 and toZMod (det JR) = 14151.
The bridge identifying JQ with the FlowFamily `jacobianEntry` at the flat base
is NOT in this file (see Rank20Reduction).
No `simp only` on vector
literals; every literal fact is a kernel `decide +kernel` on a closed finite
statement over ZMod 65521, Fin 20 or the integer units. -/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Glennie.Compact.Rank20Certificate

noncomputable section


/-- The ring hom ℤ√3 → ZMod 65521 sending √3 to 627. -/
def phiP : ℤ√3 →+* ZMod 65521 := Zsqrtd.lift ⟨627, by decide +kernel⟩

/-- The ring hom ℤ√3 → ℝ sending √3 to Real.sqrt 3. -/
def liftR : ℤ√3 →+* ℝ := Zsqrtd.lift ⟨√3, by norm_num⟩

/-- `√3` in `ℤ√3`. -/
abbrev s : ℤ√3 := Zsqrtd.sqrtd

@[simp] theorem liftR_s : liftR s = √3 := by simp [liftR]

@[simp] theorem liftR_ofNat (n : ℕ) [n.AtLeastTwo] : liftR (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  map_ofNat liftR n

/-- 72 times the flat-base derivative matrix. -/
def JZ : Matrix (Fin 20) (Fin 20) (ℤ√3) :=
  !![0, 0, 2, 2 * s, -2, 2 * s, s, -1, 0, 0, -2, 0, 2 * s, 2, 0, 0, -s, 1, 4, 0;
     0, 0, 2, 2 * s, 4, 0, -s, -1, 0, 0, 1, s, 0, -4, 0, 0, s, 1, -2, -2 * s;
     0, 0, 2, 2 * s, -2, -2 * s, 0, 2, 0, 0, 1, -s, -2 * s, 2, 0, 0, 0, -2, -2, 2 * s;
     0, 0, -4, 0, -2, 2 * s, -s, -1, 0, 0, 1, -s, 2 * s, 2, 0, 0, s, 1, -2, 2 * s;
     0, 0, -4, 0, 4, 0, 0, 2, 0, 0, -2, 0, 0, -4, 0, 0, 0, -2, 4, 0;
     0, 0, -4, 0, -2, -2 * s, s, -1, 0, 0, 1, s, -2 * s, 2, 0, 0, -s, 1, -2, -2 * s;
     0, 0, 2, -2 * s, -2, 2 * s, 0, 2, 0, 0, 1, s, 2 * s, 2, 0, 0, 0, -2, -2, -2 * s;
     0, 0, 2, -2 * s, 4, 0, s, -1, 0, 0, 1, -s, 0, -4, 0, 0, -s, 1, -2, 2 * s;
     -4 * s, -4, 0, 0, 2, -2 * s, 0, 0, -4, 0, 2, 0, 0, 0, 2, 2 * s, -s, 1, 4, 0;
     -4 * s, -4, 0, 0, -4, 0, 0, 0, 2, 2 * s, -1, -s, 0, 0, 2, -2 * s, s, 1, -2, -2 * s;
     -4 * s, -4, 0, 0, 2, 2 * s, 0, 0, 2, -2 * s, -1, s, 0, 0, -4, 0, 0, -2, -2, 2 * s;
     0, 8, 0, 0, 2, -2 * s, 0, 0, 2, -2 * s, -1, s, 0, 0, 2, -2 * s, s, 1, -2, 2 * s;
     0, 8, 0, 0, -4, 0, 0, 0, -4, 0, 2, 0, 0, 0, -4, 0, 0, -2, 4, 0;
     0, 8, 0, 0, 2, 2 * s, 0, 0, 2, 2 * s, -1, -s, 0, 0, 2, 2 * s, -s, 1, -2, -2 * s;
     4 * s, -4, 0, 0, 2, -2 * s, 0, 0, 2, 2 * s, -1, -s, 0, 0, -4, 0, 0, -2, -2, -2 * s;
     4 * s, -4, 0, 0, -4, 0, 0, 0, 2, -2 * s, -1, s, 0, 0, 2, 2 * s, -s, 1, -2, 2 * s;
     4 * s, 4, -2, -2 * s, 0, 0, -s, 1, 4, 0, 0, 0, -2 * s, -2, -2, -2 * s, 0, 0, 0, 0;
     4 * s, 4, -2, -2 * s, 0, 0, s, 1, -2, -2 * s, 0, 0, 0, 4, -2, 2 * s, 0, 0, 0, 0;
     0, -8, 4, 0, 0, 0, s, 1, -2, 2 * s, 0, 0, -2 * s, -2, -2, 2 * s, 0, 0, 0, 0;
     0, -8, 4, 0, 0, 0, 0, -2, 4, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0, 0]

/-- An inverse of `JZ` modulo 65521. -/
def Binv : Matrix (Fin 20) (Fin 20) (ZMod 65521) :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 27283, 27283, 27283, 46402, 46402, 46402, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62791, 62791, 62791, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 5460, 5460, 5460, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     10955, 10955, 10955, 38238, 38238, 38238, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 5460, 0, 0, 5460, 0, 0, 5460, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 54566, 27283, 0, 54566, 27283, 0, 54566, 27283, 0, 0, 0, 0;
     21910, 49193, 10955, 49193, 60148, 21910, 10955, 21910, 0, 49193, 0, 49193, 49193, 0, 0, 0, 0, 49193, 49193, 49193;
     54601, 60061, 54601, 60061, 60061, 0, 54601, 0, 54601, 60061, 0, 60061, 5460, 0, 0, 0, 54601, 60061, 60061, 5460;
     54601, 54601, 60061, 54601, 54601, 60061, 60061, 60061, 54601, 54601, 60061, 54601, 54601, 60061, 60061, 60061, 54601, 60061, 60061, 54601;
     0, 54566, 27283, 10955, 0, 38238, 38238, 27283, 0, 54566, 27283, 10955, 0, 38238, 38238, 27283, 0, 16328, 49193, 0;
     54601, 49141, 54601, 49141, 54601, 54601, 54601, 54601, 54601, 60061, 0, 60061, 54601, 0, 0, 0, 54601, 60061, 60061, 54601;
     0, 27283, 54566, 38238, 0, 10955, 10955, 54566, 0, 16328, 0, 49193, 0, 0, 0, 0, 0, 16328, 49193, 0;
     10955, 38238, 0, 10955, 38238, 0, 10955, 38238, 10955, 38238, 0, 10955, 38238, 0, 10955, 38238, 0, 0, 0, 0;
     0, 5460, 0, 0, 5460, 0, 0, 5460, 0, 5460, 0, 0, 5460, 0, 0, 5460, 0, 0, 0, 0;
     5460, 2730, 0, 2730, 62791, 0, 0, 0, 5460, 2730, 5460, 2730, 2730, 0, 5460, 0, 5460, 2730, 2730, 62791;
     0, 57357, 0, 57357, 57357, 0, 0, 0, 10955, 57357, 38238, 57357, 30074, 10955, 38238, 10955, 0, 57357, 57357, 57357;
     0, 49193, 0, 49193, 49193, 0, 0, 0, 0, 49193, 0, 49193, 49193, 0, 0, 0, 0, 49193, 49193, 49193;
     54601, 60061, 0, 60061, 5460, 0, 0, 0, 54601, 60061, 0, 60061, 5460, 0, 0, 0, 54601, 60061, 60061, 5460;
     60061, 62791, 0, 62791, 60061, 0, 0, 0, 60061, 62791, 0, 62791, 60061, 0, 0, 0, 60061, 62791, 62791, 60061;
     0, 8164, 0, 57357, 0, 0, 0, 0, 0, 8164, 0, 57357, 0, 0, 0, 0, 0, 8164, 57357, 0]

/-- The real flat-base matrix J. -/
def JQ : Matrix (Fin 20) (Fin 20) ℝ :=
  Matrix.of fun r n => liftR (JZ r n) / 72

/-- The real 20x20 minor is nonsingular. -/
theorem det_JQ_ne_zero : JQ.det ≠ 0 := by
  have hJ : JQ = (72 : ℝ)⁻¹ • JZ.map liftR := by ext <;> simp [JQ, div_eq_inv_mul]
  have := Fact.mk (by norm_num : 1 < 65521)
  have h := Matrix.det_ne_zero_of_right_inverse (show JZ.map phiP * Binv = 1 by decide +kernel)
  rw [hJ, Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  refine mul_ne_zero (by norm_num) fun h' => h ?_
  rw [Zsqrtd.lift_injective _ (fun n h => by
    have : n < 2 := by nlinarith
    have : -2 < n := by nlinarith
    interval_cases n <;> omega) (h'.trans (map_zero _).symm), map_zero]

end
end Glennie.Compact.Rank20Certificate
