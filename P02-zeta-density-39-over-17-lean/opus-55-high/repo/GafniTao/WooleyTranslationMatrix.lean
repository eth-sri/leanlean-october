module
public import GafniTao.WooleySection7MomentIdentity
public import Mathlib.LinearAlgebra.Matrix.Block
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# The integral translation matrix in Wooley Section 7

The passage from (7.6) to (7.7) translates every variable by the right
residue representative and then makes a triangular integral change of the
equations.  This file records the first, source-visible part of that change.
The matrix below is the positive-degree coefficient matrix of
`(X + eta)^(j+1)`; it is upper triangular with diagonal one and hence is a
unit over every residue ring.
-/

open Finset Polynomial Matrix

namespace GafniTao

noncomputable section

/-- Positive-degree translation matrix, with zero-based matrix indices. -/
def wooleyPolynomialTranslationMatrix (k q : ℕ) (eta : ℤ) :
    Matrix (Fin k) (Fin k) (ZMod q) :=
  fun i j =>
    if (i : ℕ) ≤ (j : ℕ) then
      (Nat.choose ((j : ℕ) + 1) ((i : ℕ) + 1) : ZMod q) *
        (eta : ZMod q) ^ ((j : ℕ) - (i : ℕ))
    else 0

section
variable (k q : ℕ) (eta : ℤ)
include k q eta
theorem wooleyPolynomialTranslationMatrix_blockTriangular :
    (wooleyPolynomialTranslationMatrix k q eta).BlockTriangular id := by
  intro i j hji
  unfold wooleyPolynomialTranslationMatrix
  rw [ite_eq_right]
  grind

@[simp] theorem wooleyPolynomialTranslationMatrix_diag (i : Fin k) :
    wooleyPolynomialTranslationMatrix k q eta i i = 1 := by
  simp [wooleyPolynomialTranslationMatrix]

theorem wooleyPolynomialTranslationMatrix_det :
    (wooleyPolynomialTranslationMatrix k q eta).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular
    (wooleyPolynomialTranslationMatrix_blockTriangular k q eta)]
  simp

theorem wooleyPolynomialTranslationMatrix_isUnit :
    IsUnit (wooleyPolynomialTranslationMatrix k q eta) := by
  rw [Matrix.isUnit_iff_isUnit_det,
    wooleyPolynomialTranslationMatrix_det]
  exact isUnit_one
end

section
variable {k p c : ℕ} {phi : WooleyPolynomialSystem k} (hphi : phi.Spaced p c) (hc : 1 ≤ c) (eta : ℤ)
include k p c phi hphi hc eta
/-- Modulo `p`, translating a `p^c`-spaced system with `c ≥ 1` gives exactly
the triangular translation matrix on its positive coefficients. -/
theorem wooleyAffinePolynomialSystem_lowMatrixMod_prime :
    wooleyPolynomialSystemLowMatrixMod
        (wooleyAffinePolynomialSystem phi 1 eta) p =
      wooleyPolynomialTranslationMatrix k p eta := by
  obtain ⟨tail, htail⟩ := hphi
  ext i j
  unfold wooleyPolynomialSystemLowMatrixMod
    wooleyPolynomialSystemLowMatrix
  rw [wooleyPolynomialLowPart_coeff (by omega)]
  pm_2849
  have hpPow : (p : ZMod p) ^ c = 0 := by
    rw [ZMod.natCast_self, zero_pow (by omega)]
  push_cast
  rw [hpPow, zero_mul, add_zero]
  unfold wooleyPolynomialTranslationMatrix
  by_cases hij : (i : ℕ) ≤ (j : ℕ)
  · rw [ite_eq_left hij]
    ring
  · rw [ite_eq_right hij]
    have hlt : (j : ℕ) + 1 < (i : ℕ) + 1 := by omega
    rw [Nat.choose_eq_zero_of_lt hlt]
    simp

/-- The translated positive low matrix is invertible modulo `p`. -/
theorem wooleyAffinePolynomialSystem_lowMatrixMod_prime_isUnit :
    IsUnit (wooleyPolynomialSystemLowMatrixMod
      (wooleyAffinePolynomialSystem phi 1 eta) p) := by
  rw [wooleyAffinePolynomialSystem_lowMatrixMod_prime hphi hc]
  exact wooleyPolynomialTranslationMatrix_isUnit k p eta
end

section
variable {k p c B : ℕ} {phi : WooleyPolynomialSystem k} (hphi : phi.Spaced p c) (hc : 1 ≤ c) (eta : ℤ)
include k p c B phi hphi hc eta
/-- Invertibility modulo the prime lifts to every working prime power. -/
theorem wooleyAffinePolynomialSystem_lowMatrixMod_primePower_isUnit :
    IsUnit (wooleyPolynomialSystemLowMatrixMod
      (wooleyAffinePolynomialSystem phi 1 eta) (p ^ B)) := by
  let A : Matrix (Fin k) (Fin k) ℤ :=
    wooleyPolynomialSystemLowMatrix
      (wooleyAffinePolynomialSystem phi 1 eta)
  have hunitpMatrix : IsUnit (wooleyIntMatrixMod A p) := by
    change IsUnit (wooleyPolynomialSystemLowMatrixMod
      (wooleyAffinePolynomialSystem phi 1 eta) p)
    exact wooleyAffinePolynomialSystem_lowMatrixMod_prime_isUnit hphi hc eta
  have hunitpDet : IsUnit (A.det : ZMod p) := by
    rw [wooleyIntMatrixMod_det]
    rw [← Matrix.isUnit_iff_isUnit_det]
    exact hunitpMatrix
  pm_8463 A.det hunitpDet
  have hunitPowDet : IsUnit (A.det : ZMod (p ^ B)) :=
    (ZMod.coe_int_isUnit_iff_isCoprime A.det (p ^ B)).mpr (by
      simpa only [Int.natCast_pow] using hcoprime.pow_left (m := B))
  rw [Matrix.isUnit_iff_isUnit_det]
  change IsUnit (wooleyIntMatrixMod A (p ^ B)).det
  rw [← wooleyIntMatrixMod_det]
  exact hunitPowDet

/-- The transpose convention is the one used for row operations on source
equations. -/
theorem wooleyAffinePolynomialSystem_exists_lowMatrix_leftInverse :
    ∃ G : Matrix (Fin k) (Fin k) (ZMod (p ^ B)),
      G * Matrix.transpose
        (wooleyPolynomialSystemLowMatrixMod
          (wooleyAffinePolynomialSystem phi 1 eta) (p ^ B)) = 1 := by
  have hunit := wooleyAffinePolynomialSystem_lowMatrixMod_primePower_isUnit
    (B := B) hphi hc eta
  have hunitT : IsUnit (Matrix.transpose
      (wooleyPolynomialSystemLowMatrixMod
        (wooleyAffinePolynomialSystem phi 1 eta) (p ^ B))) := by
    pm_8067
  pm_969 k B
end

/-- Translation does not create a degree-above-`k` coefficient outside the
original `p^c`-divisible tail. -/
theorem WooleyPolynomialSystem.Spaced.affine_one_high_coeff_dvd
    {k p c : ℕ} {phi : WooleyPolynomialSystem k}
    (hphi : phi.Spaced p c) (eta : ℤ) (j : Fin k) (n : ℕ)
    (hn : k + 1 ≤ n) :
    (p : ℤ) ^ c ∣
      (wooleyAffinePolynomialSystem phi 1 eta j).coeff n := by
  obtain ⟨tail, htail⟩ := hphi
  pm_2849
  have hjlt : (j : ℕ) + 1 < n := by omega
  rw [Nat.choose_eq_zero_of_lt hjlt]
  simp only [Nat.cast_zero]
  refine ⟨((tail j).comp (X + C eta)).coeff n, ?_⟩
  ring


end

end GafniTao
