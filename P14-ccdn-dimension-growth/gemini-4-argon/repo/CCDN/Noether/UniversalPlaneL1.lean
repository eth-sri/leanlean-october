/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ForMathlib.IntegerPolynomialL1
public import CCDN.Noether.AmbientNoetherForms
import CCDN.Noether.AmbientNoetherVanishing
import CCDN.Noether.EulerSparseMatrix

/-! Explicit coefficient-sum bounds for generic plane restrictions.
An original monomial of degree d contributes at most 3^d; an Euler matrix
entry contributes at most d times this quantity. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- For a monomial of degree `k + 2`, every Euler matrix entry of its universal plane restriction
has coefficient ℓ¹-norm at most `(k + 2) * 3 ^ (k + 2)`. -/
theorem ambientEulerEntry_monomial_l1_le {σ : Type*} (k : ℕ)
    (m : σ →₀ ℕ) (hm : m.degree = k + 2) (row : ℕ × ℕ) (col : EulerColumns k) :
    l1Norm (ambientEulerEntryLinear ℤ σ k row col (monomial m 1)) ≤
      (k + 2) * 3 ^ (k + 2) := by
  classical
  rw [ambientEulerEntryLinear_apply]
  let f := universalPlanePolynomial (monomial m (1 : ℤ))
  have hf : bivariateTotalDegree f ≤ k + 2 :=
    (universalPlanePolynomial_totalDegree_le _).trans
      ((totalDegree_monomial_le m (1 : ℤ)).trans (by change m.degree ≤ k + 2; omega))
  have he := congrFun (congrFun (universalEulerMatrix_specialize k f hf) row) col
  change eval₂Hom (Int.castRingHom (MvPolynomial (PlaneParameters σ) ℤ))
    (eulerCoefficientData (k + 2) f) (universalEulerMatrix k row col) = _ at he
  rw [← he]
  obtain hz | ⟨i, c, hc, hm_sparse⟩ := universalEulerMatrix_sparse k row col
  · rw [hz, map_zero, l1Norm_zero]; exact Nat.zero_le _
  · rw [hm_sparse, map_mul, eval₂Hom_C, show eval₂Hom (Int.castRingHom (MvPolynomial (PlaneParameters σ) ℤ))
        (eulerCoefficientData (k + 2) f) (X i) = eulerCoefficientData (k + 2) f i from eval₂_X _ _ _]
    change l1Norm (C c * eulerCoefficientData (k + 2) f i) ≤ _
    refine (l1Norm_mul_le _ _).trans ?_
    rw [l1Norm_C]
    refine Nat.mul_le_mul (by exact_mod_cast (show (c.natAbs : ℤ) ≤ (k + 2 : ℕ) by
      simpa only [Int.natCast_natAbs] using hc)) ?_
    simp only [f, eulerCoefficientData, universalPlanePolynomial, AlgEquiv.symm_apply_apply]
    refine (l1Norm_coeff_le_l1Norm_sumAlgEquiv_symm _ _).trans ?_
    rw [universalPlaneMap, aeval_monomial, map_one, one_mul]
    change l1Norm ((sumAlgEquiv ℤ (Fin 2) (PlaneParameters σ)).symm
      (∏ j ∈ m.support, (C (X (j, 0)) + C (X (j, 1)) * X 0 + C (X (j, 2)) * X 1) ^ m j)) ≤ _
    rw [map_prod, ← hm]
    simp only [map_pow]
    have hcoord (j : σ) :
        l1Norm ((sumAlgEquiv ℤ (Fin 2) (PlaneParameters σ)).symm
          (C (X (j, 0)) + C (X (j, 1)) * X 0 + C (X (j, 2)) * X 1)) ≤ 3 := by
      simp only [map_add, map_mul, sumAlgEquiv_symm_C_X, sumAlgEquiv_symm_X]
      have hx (p : Fin 2 ⊕ PlaneParameters σ) :
          l1Norm (X p : MvPolynomial (Fin 2 ⊕ PlaneParameters σ) ℤ) = 1 := by simp [X]
      have hab := (l1Norm_add_le (X (Sum.inr (j, 0)) : MvPolynomial (Fin 2 ⊕ PlaneParameters σ) ℤ)
        (X (Sum.inr (j, 1)) * X (Sum.inl 0))).trans (Nat.add_le_add_left (l1Norm_mul_le _ _) _)
      have hc_mul := l1Norm_mul_le (X (Sum.inr (j, 2)) : MvPolynomial (Fin 2 ⊕ PlaneParameters σ) ℤ)
        (X (Sum.inl 1))
      refine (l1Norm_add_le _ _).trans ?_
      simpa only [hx] using Nat.add_le_add hab hc_mul
    exact (l1Norm_prod_le _ _).trans
      ((Finset.prod_le_prod fun j _ =>
        (l1Norm_pow_le _ _).trans (Nat.pow_le_pow_left (hcoord j) _)).trans_eq
        (by rw [Finset.prod_pow_eq_pow_sum]; rfl))

end
end CCDN
