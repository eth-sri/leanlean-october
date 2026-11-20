/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ForMathlib.Matrix
public import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Module.Projective
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Tactic.Positivity

/-! Integral column-lattice factorization and the complementary-minor bound for a basis of
 the integral kernel. -/

@[expose] public section
namespace CCDN
noncomputable section
open Matrix Module Finset

section

variable {k : ℕ} {ι : Type*} [Fintype ι] (A : Matrix (Fin k) ι ℤ)
include k ι A

/-- Factor the columns through a square matrix whose image is their lattice. -/
theorem integer_square_column_factorization :
    ∃ (B : Matrix (Fin k) (Fin k) ℤ) (R : Matrix (Fin k) ι ℤ) (C : Matrix ι (Fin k) ℤ),
      A = B * R ∧ B = A * C := by
  classical
  let L := LinearMap.range A.mulVecLin
  obtain ⟨r, snf⟩ := L.smithNormalForm (Pi.basisFun ℤ (Fin k))
  let T := snf.bN.equivFun.symm.toLinearMap.comp
    ((LinearMap.funLeft ℤ ℤ snf.f).comp snf.bM.equivFun.toLinearMap)
  have hT : Function.Surjective T := snf.bN.equivFun.symm.surjective.comp
    ((LinearMap.funLeft_surjective_of_injective ℤ ℤ _ snf.f.injective).comp snf.bM.equivFun.surjective)
  let A' := A.mulVecLin.rangeRestrict
  obtain ⟨R, hR⟩ := Module.projective_lifting_property T A' hT
  obtain ⟨C, hC⟩ := Module.projective_lifting_property A' T (LinearMap.surjective_rangeRestrict _)
  have hsub : L.subtype.comp A' = A.toLin' := rfl
  refine ⟨(L.subtype.comp T).toMatrix', R.toMatrix', C.toMatrix', ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, LinearMap.comp_assoc, hR, hsub, LinearMap.toMatrix'_toLin']
  · rw [← LinearMap.toMatrix'_toLin' A, ← LinearMap.toMatrix'_comp, ← hsub,
      LinearMap.comp_assoc, hC]

/-- Divisibility of all maximal minors passes to the square column factor. -/
theorem dvd_det_square_column_factor (C : Matrix ι (Fin k) ℤ) (d : ℤ)
    (hd : ∀ c : Fin k ↪ ι, d ∣ (A.submatrix id c).det) : d ∣ (A * C).det := by
  rw [← det_transpose, transpose_mul]
  apply dvd_det_mul_of_row_minors
  intro c
  rw [← det_transpose, transpose_submatrix, transpose_transpose]
  exact hd c

end

/-- The common nonnegative divisor of all maximal minors, including zero minors. -/
def minorGcd {m N : ℕ} (A : Matrix (Fin m) (Fin N) ℤ) : ℤ :=
  univ.gcd (fun c : Fin m → Fin N => (A.submatrix id c).det)

section

variable {m N : ℕ} (A : Matrix (Fin m) (Fin N) ℤ)
include m N A

lemma dvd_minorGcd {x : ℤ} :
    x ∣ minorGcd A ↔ ∀ c : Fin m → Fin N, x ∣ (A.submatrix id c).det := by
  simp [minorGcd, Finset.dvd_gcd_iff]

lemma minorGcd_dvd_det (c : Fin m → Fin N) :
    minorGcd A ∣ (A.submatrix id c).det :=
  (dvd_minorGcd A).mp dvd_rfl c

private lemma minorGcd_nonneg :
    0 ≤ minorGcd A := by
  calc
    _ ≤ |minorGcd A| := abs_nonneg _
    _ = _ := (Int.abs_eq_normalize _).trans Finset.normalize_gcd

end

private lemma exists_integer_submatrix_det_ne_zero {m N : ℕ} {A : Matrix (Fin m) (Fin N) ℤ}
    (hi : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) :
    ∃ c : Fin m → Fin N, (A.submatrix id c).det ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_det_submatrix_ne_zero_of_linearIndependent_row _ hi
  refine ⟨c, fun h => hc ?_⟩
  change ((Int.castRingHom ℚ).mapMatrix (A.submatrix id c)).det = 0
  rw [← RingHom.map_det, h, map_zero]

lemma one_le_minorGcd {m N : ℕ} {A : Matrix (Fin m) (Fin N) ℤ}
    (hi : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) : 1 ≤ minorGcd A := by
  obtain ⟨c, hc⟩ := exists_integer_submatrix_det_ne_zero hi
  have hg := ne_zero_of_dvd_ne_zero hc (minorGcd_dvd_det A c)
  have := minorGcd_nonneg A
  omega

lemma minorGcd_square {s : ℕ} (A : Matrix (Fin s) (Fin s) ℤ) :
    minorGcd A = |A.det| := by
  classical
  refine Int.dvd_antisymm (minorGcd_nonneg A) (abs_nonneg _) ?_ ?_
  · rw [dvd_abs]
    simpa using minorGcd_dvd_det A id
  · rw [dvd_minorGcd]
    intro c
    by_cases hi : Function.Injective c
    · let e := Equiv.ofBijective c (Finite.injective_iff_bijective.mp hi)
      have he := abs_det_submatrix_equiv_equiv (Equiv.refl _) e A
      change |(A.submatrix id c).det| = _ at he
      rw [← dvd_abs, he]
    · obtain ⟨i, j, he, hne⟩ := Function.not_injective_iff.mp hi
      rw [det_zero_of_column_eq (M := A.submatrix id c) hne (fun i => congrArg (A i) he)]
      exact dvd_zero _

/-- Complete the chosen columns of a complementary minor to a reindexing of the matrix. -/
private lemma exists_complement_reindex {s k N : ℕ} (h : s + k = N)
    (c : Fin k → Fin N) (hc : Function.Injective c) :
    ∃ e : Fin s ⊕ Fin k ≃ Fin N, e ∘ Sum.inr = c := by
  classical
  let R := Set.range c
  let d := Equiv.ofInjective c hc
  let e₀ := (Equiv.sumComm (Rᶜ : Set (Fin N)) R).trans (Equiv.Set.sumCompl R)
  have hs : Fintype.card (Rᶜ : Set (Fin N)) = s := by
    have H := Fintype.card_congr e₀
    rw [Fintype.card_sum, ← Fintype.card_congr d, Fintype.card_fin, Fintype.card_fin] at H
    omega
  exact ⟨(Equiv.sumCongr (Fintype.equivFinOfCardEq hs).symm d).trans e₀, rfl⟩

/-- A basis matrix of the integral kernel gives both the rank deficit and a complementary
minor bound. Factoring through the column lattice extracts the gcd. -/
lemma complement_minor_bound {s k N : ℕ} (A : Matrix (Fin s) (Fin N) ℤ)
    (K : Matrix (Fin N) (Fin k) ℤ) (hi : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row)
    (hker : ∀ v, A *ᵥ v = 0 ↔ ∃ u, K *ᵥ u = v) (c : Fin k → Fin N)
    (hc : Function.Injective c) (hc0 : (K.submatrix c id).det ≠ 0) :
    s + k = N ∧ ∃ a : Fin s → Fin N,
      minorGcd A * |(K.submatrix c id).det| ≤ |(A.submatrix id a).det| := by
  classical
  obtain ⟨B, R, C, hfac, hgen⟩ := integer_square_column_factorization A
  obtain ⟨j, hj⟩ := exists_integer_submatrix_det_ne_zero hi
  have hB : B.det ≠ 0 := fun hzero => hj (by
    rw [hfac]
    change (B * R.submatrix id j).det = 0
    simp [det_mul, hzero])
  have hAK : A * K = 0 := by
    apply mulVec_injective
    funext v
    rw [← mulVec_mulVec, zero_mulVec]
    exact (hker _).mpr ⟨_, rfl⟩
  let T := fromCols C K
  have hsurj : Function.Surjective T.mulVecLin := by
    intro y
    have hy : A *ᵥ (y - C *ᵥ (R *ᵥ y)) = 0 := by
      rw [mulVec_sub, mulVec_mulVec, mulVec_mulVec, ← hgen, ← hfac, sub_self]
    obtain ⟨v, hv⟩ := (hker _).mp hy
    refine ⟨Sum.elim (R *ᵥ y) v, ?_⟩
    change T *ᵥ Sum.elim _ _ = _
    dsimp only [T]
    rw [fromCols_mulVec_sumElim, hv, add_sub_cancel]
  let D := (1 : Matrix (Fin N) (Fin N) ℤ).submatrix c id
  let W₀ := fromRows A D
  have hD {l : ℕ} (M : Matrix (Fin N) (Fin l) ℤ) : D * M = M.submatrix c id := by
    rw [show D * M = ((1 : Matrix (Fin N) (Fin N) ℤ) * M).submatrix c id from
      submatrix_mul_equiv _ M _ (Equiv.refl _) _, Matrix.one_mul]
  have hW₀ : W₀ * T = fromBlocks B 0 (C.submatrix c id) (K.submatrix c id) := by
    simp only [W₀, T, fromRows_mul_fromCols, ← hgen, hAK, hD]
  have hinj : Function.Injective T.mulVecLin := by
    refine Function.Injective.of_comp (f := W₀.mulVecLin) ?_
    change Function.Injective (fun x => W₀ *ᵥ (T *ᵥ x))
    simp only [mulVec_mulVec]
    apply Matrix.mulVec_injective_of_det_ne_zero
    rw [hW₀, det_fromBlocks_zero₁₂]
    exact mul_ne_zero hB hc0
  have hcard : s + k = N := by
    simpa using (LinearEquiv.ofBijective T.mulVecLin ⟨hinj, hsurj⟩).finrank_eq
  obtain ⟨e, he⟩ := exists_complement_reindex hcard c hc
  refine ⟨hcard, e ∘ Sum.inl, ?_⟩
  let U := T.submatrix e id
  have hu : Function.Surjective U.mulVecLin := by
    change Function.Surjective ((Matrix.reindex e.symm (Equiv.refl _) T).mulVecLin)
    rw [Matrix.mulVecLin_reindex]
    exact (LinearEquiv.funCongrLeft ℤ ℤ e).surjective.comp (hsurj.comp fun x => ⟨x, rfl⟩)
  have hU : |U.det| = 1 := by
    rw [← Int.isUnit_iff_abs_eq, ← isUnit_iff_isUnit_det, ← mulVec_surjective_iff_isUnit]
    exact hu
  let W := W₀.submatrix id e
  have hWdet : W.det = (A.submatrix id (e ∘ Sum.inl)).det := by
    rw [show W = fromBlocks (A.submatrix id (e ∘ Sum.inl)) (A.submatrix id (e ∘ Sum.inr)) 0 1 by
      ext (i | i) (j | j) <;> simp [W, W₀, D, ← he, Matrix.one_apply, e.injective.eq_iff],
      det_fromBlocks_zero₂₁, det_one, mul_one]
  have hW : W * U = W₀ * T := by
    simp [W, U, submatrix_mul_equiv W₀ T id e id]
  have hdet := congrArg (fun M : Matrix (Fin s ⊕ Fin k) (Fin s ⊕ Fin k) ℤ => |M.det|) hW
  simp only [hW₀, det_mul, abs_mul, hU, mul_one, hWdet, det_fromBlocks_zero₁₂] at hdet
  rw [hdet]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  apply Int.le_of_dvd (abs_pos.mpr hB)
  rw [dvd_abs, hgen]
  exact dvd_det_square_column_factor A C _ (fun c => minorGcd_dvd_det A c)

end
end CCDN
