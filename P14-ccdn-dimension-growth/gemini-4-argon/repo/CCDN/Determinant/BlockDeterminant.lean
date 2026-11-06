/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import ArithmeticHeights.BombieriVaaler
import all ArithmeticHeights.BombieriVaaler
import CCDN.ForMathlib.Matrix

/-! Combining maximal-minor divisibility across row blocks. -/

@[expose] public section
namespace CCDN
noncomputable section
open Matrix Module Finset

/-- Enumerate rows grouped by their residue-class label. -/
private def partitionRowEquiv {c s : ℕ} (label : Fin s → Fin c) :
    (Σ i : Fin c, Fin (Fintype.card {j : Fin s // label j = i})) ≃ Fin s :=
  (Equiv.sigmaCongrRight fun i =>
    (Fintype.equivFin {j : Fin s // label j = i}).symm).trans (Equiv.sigmaFiberEquiv label)

/-- An enumeration of the rows `j` with `label j = i`, the `i`-th block of the partition of the rows
determined by `label`. -/
def residueRows {c s : ℕ} (label : Fin s → Fin c) (i : Fin c) :
    Fin (Fintype.card {j : Fin s // label j = i}) → Fin s :=
  fun j => ((Fintype.equivFin {j : Fin s // label j = i}).symm j).val

/-- Every row enumerated by `residueRows label i` has label `i`. -/
lemma residueRows_label {c s : ℕ} (label : Fin s → Fin c) (i : Fin c)
    (j : Fin (Fintype.card {j : Fin s // label j = i})) :
    label (residueRows label i j) = i :=
  ((Fintype.equivFin {j : Fin s // label j = i}).symm j).property

/-- The sizes of the classes of a labelling `label : Fin s → Fin c` add up to `s`. -/
lemma sum_residue_class_sizes {c s : ℕ} (label : Fin s → Fin c) :
    (∑ i : Fin c, Fintype.card {j : Fin s // label j = i}) = s := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using Fintype.card_congr (partitionRowEquiv label)

/-- `Int.Matrix.minorGcd` is the gcd of the Plücker coordinates of the rows. The vendored
definition is not exposed; this module imports its body (`import all`) so that the rest of the
library can rewrite with this lemma instead. -/
theorem minorGcd_eq_gcd_plucker {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}
    (A : Matrix (Fin m) ι ℤ) :
    Int.Matrix.minorGcd A = (univ : Finset (Set.powersetCard ι m)).gcd
      (exteriorPower.plucker m A.row) := by
  rw [Int.Matrix.minorGcd]

/-- If the rows of an integer matrix `A` are partitioned into blocks by `label`, and for each block
`i` the power `p ^ e i` divides every maximal minor of the block's rows, then `p ^ (∑ i, e i)`
divides the gcd of the maximal minors of `A`. -/
theorem residue_prime_powers_dvd_minorGcd {c s N : ℕ}
    (A : Matrix (Fin s) (Fin N) ℤ) (label : Fin s → Fin c)
    (p : ℤ) (e : Fin c → ℕ)
    (he : ∀ i, ∀ j : Fin (Fintype.card {j : Fin s // label j = i}) → Fin N,
      p ^ e i ∣ (A.submatrix (residueRows label i) j).det) :
    p ^ (∑ i, e i) ∣ Int.Matrix.minorGcd A := by
  classical
  have hsq_fac {k M : ℕ} (D : Matrix (Fin k) (Fin M) ℤ) :
      ∃ (B : Matrix (Fin k) (Fin k) ℤ) (R : Matrix (Fin k) (Fin M) ℤ)
        (C : Matrix (Fin M) (Fin k) ℤ), D = B * R ∧ B = D * C := by
    let L := LinearMap.range D.mulVecLin
    obtain ⟨r, snf⟩ := L.smithNormalForm (Pi.basisFun ℤ (Fin k))
    let T : (Fin k → ℤ) →ₗ[ℤ] L :=
      { toFun := fun x => snf.bN.equivFun.symm (fun i => snf.bM.repr x (snf.f i))
        map_add' := fun x y => by
          rw [← map_add]; congr 1; ext i
          exact congrArg (fun v : Fin k →₀ ℤ => v (snf.f i)) (snf.bM.repr.map_add x y)
        map_smul' := fun a x => by
          rw [← map_smul]; congr 1; ext i
          exact congrArg (fun v : Fin k →₀ ℤ => v (snf.f i)) (snf.bM.repr.map_smul a x) }
    have hT : Function.Surjective T := fun y => by
      refine ⟨∑ i : Fin r, snf.bN.repr y i • snf.bM (snf.f i), ?_⟩
      apply (snf.bN.equivFun.symm_apply_eq).mpr
      funext j
      simp only [map_sum, map_smul, Basis.repr_self]
      simp [Basis.equivFun_apply]
      simp [Finsupp.single_apply, snf.f.injective.eq_iff]
    let B := LinearMap.toMatrix' (L.subtype.comp T)
    have hB (x : Fin k → ℤ) : B *ᵥ x = (T x : Fin k → ℤ) :=
      LinearMap.toMatrix'_mulVec (L.subtype.comp T) x
    choose R hR using fun j : Fin M =>
      show ∃ x : Fin k → ℤ, B *ᵥ x = D.col j by
        obtain ⟨x, hx⟩ := hT ⟨D.col j, by
          rw [show L = LinearMap.range D.mulVecLin from rfl, Matrix.range_mulVecLin]
          exact Submodule.subset_span ⟨j, rfl⟩⟩
        exact ⟨x, (hB x).trans (congrArg Subtype.val hx)⟩
    choose C hC using fun j : Fin k =>
      show ∃ x : Fin M → ℤ, D *ᵥ x = B.col j by
        rw [show B.col j = (T (Pi.single j 1) : Fin k → ℤ) by simpa using hB (Pi.single j 1)]
        exact (T (Pi.single j 1)).property
    refine ⟨B, fun i j => R j i, fun i j => C j i, ?_, ?_⟩ <;> ext i j
    · exact (congrFun (hR j) i).symm
    · exact (congrFun (hC j) i).symm
  rw [← Finset.prod_pow_eq_pow_sum, minorGcd_eq_gcd_plucker]
  refine Finset.dvd_gcd fun S _ => ?_
  rw [Matrix.plucker_row_eq_det_submatrix]
  let A_S := A.submatrix id ((S : Finset (Fin N)).orderEmbOfFin (Set.powersetCard.card_eq S))
  let ep := partitionRowEquiv label
  rw [← Matrix.det_submatrix_equiv_self ep A_S]
  let A' := A_S.submatrix ep ep
  let eq := Fintype.equivFin (Σ i, Fin (Fintype.card {j : Fin s // label j = i}))
  let M := fun i => A'.submatrix (Sigma.mk i) eq.symm
  choose B R C hR hC using fun i => hsq_fac (M i)
  have hdiv (i : Fin c) : p ^ e i ∣ (B i).det := by
    rw [hC i, Matrix.det_mul_eq_sum_det_submatrix]
    exact Finset.dvd_sum fun T _ => dvd_mul_of_dvd_left (he i _) _
  let Q : Matrix (Σ i, Fin (Fintype.card {j : Fin s // label j = i}))
      (Σ i, Fin (Fintype.card {j : Fin s // label j = i})) ℤ :=
    fun i j => R i.1 i.2 (eq j)
  have hfac : Matrix.blockDiagonal' B * Q = A' := by
    ext ⟨i, j⟩ l
    rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single i]
    · simp only [Matrix.blockDiagonal'_apply_eq]
      simpa only [M, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.mul_apply, Q] using
        (congrArg (fun m => m j (eq l)) (hR i)).symm
    · intro k _ hki
      exact Finset.sum_eq_zero fun t _ => by
        rw [Matrix.blockDiagonal'_apply_ne B j t hki.symm, zero_mul]
    · simp
  change _ ∣ A'.det
  rw [← hfac, Matrix.det_mul, Matrix.det_blockDiagonal']
  exact dvd_mul_of_dvd_left (Finset.prod_dvd_prod_of_dvd _ _ fun i _ => hdiv i) _

end
end CCDN
