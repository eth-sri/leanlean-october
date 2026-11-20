/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Determinant.MinorGcd
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Int.Order.Units

@[expose] public section
namespace CCDN
noncomputable section
open Matrix Module

variable {s N k : ℕ} (A : Matrix (Fin s) (Fin N) ℤ)

private theorem exists_full_factor (hi : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) :
    ∃ (P : Matrix (Fin N) (Fin s) ℤ) (W : Matrix (Fin s) (Fin N) ℤ),
      A * P * W = A ∧ (A * P).det ≠ 0 := by
  obtain ⟨P,W,h⟩ := integer_square_column_factorization A
  let φ := Int.castRingHom ℚ
  refine ⟨P,W,h, ?_⟩
  have he : (A * P).map φ * W.map φ = A.map φ := by rw [← Matrix.map_mul, h]
  have hu : Function.Surjective ((A * P).map φ).mulVec := by
    intro x
    obtain ⟨v, hv⟩ := hi.mulVec_surjective x
    exact ⟨W.map φ *ᵥ v, by rw [mulVec_mulVec, he]; exact hv⟩
  have := (Matrix.isUnit_iff_isUnit_det _).mp (mulVec_surjective_iff_isUnit.mp hu)
  intro hz
  apply this.ne_zero
  change (φ.mapMatrix (A * P)).det = 0
  rw [← RingHom.map_det, hz, map_zero]

/-- Augment full-rank rows by coordinate functionals on their kernel. A minor
of an integral kernel basis times the determinantal divisor is bounded by the
absolute complementary row minor. This needs no short-vector theorem. -/
theorem complementary_minor_bound (C : Matrix (Fin N) (Fin k) ℤ)
    (hi : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row)
    (hAC : A * C = 0) (hker : ∀ v, A *ᵥ v = 0 → ∃ w, C *ᵥ w = v)
    (u : Fin k → Fin N) (hu : Function.Injective u) (hc : (C.submatrix u id).det ≠ 0) :
    s + k = N ∧ ∃ j : Fin s → Fin N, Int.Matrix.minorGcd A * |(C.submatrix u id).det| ≤
      |(A.submatrix id j).det| := by
  classical
  obtain ⟨P,W,h,hP⟩ := exists_full_factor A hi
  let Q := fromCols P C
  have hQ : Function.Surjective Q.mulVec := by
    intro v
    have hv : A *ᵥ (v - P *ᵥ (W *ᵥ v)) = 0 := by rw [mulVec_sub, mulVec_mulVec, mulVec_mulVec, h, sub_self]
    obtain ⟨z,hz⟩ := hker _ hv
    exact ⟨Sum.elim (W *ᵥ v) z, by simp [Q, hz]⟩
  have hj := (injective_iff_map_eq_zero Q.mulVecLin).mpr fun z hz => by
    change Q *ᵥ z = 0 at hz
    rw [fromCols_mulVec] at hz
    have hp := congrArg (A *ᵥ ·) hz
    simp only [mulVec_add, mulVec_mulVec, hAC, zero_mulVec, add_zero, mulVec_zero] at hp
    have h₁ := Matrix.eq_zero_of_mulVec_eq_zero hP hp
    rw [h₁, mulVec_zero, zero_add] at hz
    funext i; cases i with
    | inl i => exact congrFun h₁ i
    | inr i => exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hc (v := z ∘ Sum.inr) (funext fun i => congrFun hz _)) i
  have hdim := by simpa using (LinearEquiv.ofBijective Q.mulVecLin ⟨hj, hQ⟩).finrank_eq
  refine ⟨hdim, ?_⟩
  let S := Set.range u
  let b := Equiv.ofInjective u hu
  let a : Fin s ≃ ↥Sᶜ := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_compl_set, ← Fintype.card_congr b, Fintype.card_fin,
      Fintype.card_fin]; omega)
  let e := (Equiv.sumComm ..).trans
    ((b.sumCongr a).trans (Equiv.sumCompl (· ∈ S)))
  let j := fun i => e (Sum.inl i)
  have eu (i) : e (Sum.inr i) = u i := rfl
  have dis (i l) : u i ≠ j l := by
    intro he; cases e.injective (show e (.inr i) = e (.inl l) from he)
  let E := (1 : Matrix _ (Fin N) ℤ).submatrix u id
  let X := fromRows A E
  have huQ : |(Q.submatrix e id).det| = 1 := by
    apply Int.isUnit_iff_abs_eq.mp ((Matrix.isUnit_iff_isUnit_det _).mp (mulVec_surjective_iff_isUnit.mp ?_))
    intro v
    obtain ⟨z,hz⟩ := hQ (v ∘ e.symm)
    exact ⟨z, by ext i; exact (congrFun hz _).trans (by simp)⟩
  have hX : X.submatrix id e = fromBlocks (A.submatrix id j) (A.submatrix id u) 0 1 := by
    ext (i|i) (l|l) <;> simp [X, E, ← show (e ∘ Sum.inl) = j from rfl, eu, submatrix_apply, one_apply, hu.eq_iff]
    exact dis i l
  have hEC : E * C = C.submatrix u id := by ext i j; simp [E, mul_apply, one_apply]
  have he : (X.submatrix id e * Q.submatrix e id).det = (X * Q).det := by rw [submatrix_mul_equiv, submatrix_id_id]
  rw [det_mul, hX, det_fromBlocks_zero₂₁, det_one, mul_one] at he
  rw [fromRows_mul_fromCols, hAC, det_fromBlocks_zero₁₂, hEC] at he
  have hh := congrArg abs he
  simp only [abs_mul, huQ, mul_one] at hh
  refine ⟨j, ?_⟩
  rw [hh]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  apply Int.le_of_dvd (abs_pos.mpr hP)
  simpa using Int.Matrix.minorGcd_dvd_det_mul A P

end
end CCDN
