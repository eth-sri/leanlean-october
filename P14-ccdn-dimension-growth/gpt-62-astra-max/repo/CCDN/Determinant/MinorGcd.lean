/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.ForMathlib.Matrix
public import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.RingTheory.Int.Basic
import Mathlib.LinearAlgebra.FreeModule.PID

/-! Determinantal divisors. Indexing by all column selections avoids choosing an
ordering or orientation: repetitions contribute zero and signs do not affect the gcd. -/
@[expose] public section
namespace Matrix
/-- A common divisor of maximal row minors divides every determinant obtained by taking
linear combinations of the rows. Expand the determinant one row at a time. -/
lemma dvd_det_mul_of_row_minors {ι κ R : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [CommRing R]
    (U : Matrix ι κ R) (V : Matrix κ ι R) {d : R}
    (h : ∀ c : ι ↪ κ, d ∣ (V.submatrix c id).det) : d ∣ (U * V).det := by
  classical
  have he : U * V = fun i => ∑ j, U i j • V.row j := by ext; simp [mul_apply]
  change d ∣ detRowAlternating.toMultilinearMap _
  rw [he, MultilinearMap.map_sum]
  apply Finset.dvd_sum
  intro c _
  rw [MultilinearMap.map_smul_univ]
  apply dvd_mul_of_dvd_right
  change d ∣ (V.submatrix c id).det
  by_cases hc : Function.Injective c
  exact h ⟨c,hc⟩
  · rw [Function.Injective] at hc
    push Not at hc
    obtain ⟨i, j, hij, hne⟩ := hc
    rw [det_zero_of_row_eq hne (congrArg V hij)]
    exact dvd_zero _

end Matrix

namespace Int.Matrix
open _root_.Matrix Finset
variable {s N : ℕ} (A : _root_.Matrix (Fin s) (Fin N) ℤ)

noncomputable def minorGcd : ℤ := univ.gcd fun c : Fin s → Fin N => (A.submatrix id c).det

lemma minorGcd_nonneg : 0 ≤ minorGcd A := by
  rw [minorGcd, ← Finset.normalize_gcd, ← Int.abs_eq_normalize]; exact abs_nonneg _

lemma minorGcd_dvd (c : Fin s → Fin N) : minorGcd A ∣ (A.submatrix id c).det := gcd_dvd (mem_univ c)

lemma one_le_minorGcd {A : _root_.Matrix (Fin s) (Fin N) ℤ}
    (h : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) : 1 ≤ minorGcd A := by
  obtain ⟨c, -, hc⟩ := exists_det_submatrix_ne_zero_of_linearIndependent_row _ h
  have hn : (A.submatrix id c).det ≠ 0 := fun hz => hc (by
    change ((Int.castRingHom ℚ).mapMatrix (A.submatrix id c)).det = 0
    rw [← RingHom.map_det, hz, map_zero])
  have hD := minorGcd_dvd A c
  have := minorGcd_nonneg A
  by_contra! hl
  simp_all [show minorGcd A = 0 by omega]

/-- Multilinearity extends divisibility from the maximal minors to arbitrary integral
linear combinations of the columns. -/
lemma minorGcd_dvd_det_mul (P : _root_.Matrix (Fin N) (Fin s) ℤ) : minorGcd A ∣ (A * P).det := by
  rw [← det_transpose, transpose_mul]
  apply dvd_det_mul_of_row_minors
  intro c
  change minorGcd A ∣ (A.submatrix id c)ᵀ.det
  grind [det_transpose, minorGcd_dvd]

end Int.Matrix

namespace CCDN
noncomputable section
open Matrix Module
open LinearMap (range)

variable {s N k : ℕ} (A : Matrix (Fin s) (Fin N) ℤ)

/-- Factor a matrix through a basis of its *integral* image, lifted back to the source. -/
private theorem exists_basis_factor : ∃ (P : Matrix (Fin N) (Fin A.rank) ℤ)
    (W : Matrix (Fin A.rank) (Fin N) ℤ), A * P * W = A := by
  classical
  let f := A.mulVecLin
  let b := Module.finBasis ℤ (range f)
  choose p hp using fun i => (b i).property
  let v (j : Fin N) := f.rangeRestrict (Pi.single j 1)
  refine ⟨of (fun j i => p i j), of (fun i j => b.repr (v j) i), ?_⟩
  ext i j
  change ∑ l, (A *ᵥ p l) i * b.repr _ l = A i j
  calc
    _ = ∑ l, b.repr _ l * (b l).val i := Finset.sum_congr rfl fun l _ => by
      change f _ i * _ = _
      rw [hp, mul_comm]
    _ = _ := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v, LinearMap.rangeRestrict, LinearMap.codRestrict_apply, f, mulVecLin_apply, mulVec_single_one, col_apply] using (congrArg (fun z : range f => z.val i) (b.sum_repr (v j)))

/-- Factor through a square matrix generating the same integral column lattice. -/
theorem integer_square_column_factorization :
    ∃ (P : Matrix (Fin N) (Fin s) ℤ) (W : Matrix (Fin s) (Fin N) ℤ), A * P * W = A := by
  obtain ⟨P, W, h⟩ := exists_basis_factor A
  let i := Fin.castLEEmb (show A.rank ≤ s by simpa using A.rank_le_card_height)
  let E := (1 : Matrix _ (Fin s) ℤ).submatrix i id
  have hE : E * Eᵀ = 1 := by
    ext a b
    simp [E, mul_apply, one_apply, i.injective.eq_iff]
  refine ⟨P * E, Eᵀ * W, ?_⟩
  calc
    _ = A * P * (E * Eᵀ) * W := by simp [Matrix.mul_assoc]
    _ = A := by simp_all

end
end CCDN
