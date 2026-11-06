/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.ForMathlib.IntegerPolynomialL1
import CCDN.Noether.AmbientNoetherForms
import CCDN.Noether.AmbientNoetherVanishing
import CCDN.Noether.EulerSparseMatrix

/-! Explicit coefficient-sum bounds for generic plane restrictions.
An original monomial of degree d contributes at most 3^d; an Euler matrix
entry contributes at most d times this quantity. -/

namespace CCDN
section
open MvPolynomial

variable {σ : Type*}

theorem eulerClosedForm_entry_l1_le (k H : ℕ)
    (f : Polynomial (Polynomial (MvPolynomial σ ℤ)))
    (hf : bivariateTotalDegree f ≤ k + 2)
    (hcoeff : ∀ i, l1Norm (eulerCoefficientData (k + 2) f i) ≤ H)
    (row : ℕ × ℕ) (col : EulerColumns k) :
    l1Norm (eulerClosedFormCoefficientMatrix k f row col) ≤ (k + 2) * H := by
  have he := congrFun (congrFun (universalEulerMatrix_specialize k f hf) row) col
  change eval₂Hom (Int.castRingHom (MvPolynomial σ ℤ))
    (eulerCoefficientData (k + 2) f) (universalEulerMatrix k row col) = _ at he
  rw [← he]
  obtain hz | ⟨i,c,hc,hm⟩ : universalEulerMatrix k row col = 0 ∨
      ∃ (i : EulerLowIndex (k + 2)) (c : ℤ), |c| ≤ (k + 2 : ℕ) ∧
        universalEulerMatrix k row col = MvPolynomial.C c * MvPolynomial.X i := by
    classical
    by_cases hex : ∃ i, eulerMonomialWeight k col i ≠ 0 ∧ eulerMonomialOutput k col i = row
    · obtain ⟨i, hi, hrow⟩ := hex
      right
      refine ⟨i, eulerMonomialWeight k col i, (show |eulerMonomialWeight k col i| ≤ (k + 2 : ℕ) by
          have hi := eulerLowExponent_degree (k + 2) i
          rcases col with j | j | j
          · have hj := eulerLowExponent_degree k j
            change |(eulerLowExponent k j 1 : ℤ) - eulerLowExponent (k + 2) i 1| ≤ _
            grind
          · have hj := eulerLowExponent_degree k j
            change |(eulerLowExponent (k + 2) i 0 : ℤ) - eulerLowExponent k j 0| ≤ _
            grind
          · change |((k + 2 : ℕ) : ℤ) - eulerLowExponent (k + 2) i 0 - eulerLowExponent (k + 2) i 1| ≤ _
            grind), ?_⟩
      unfold universalEulerMatrix
      rw [Finset.sum_eq_single i]
      · simp_all [eulerClosedForm_monomial_entry]
      · intro j _ hji
        rw [eulerClosedForm_monomial_entry]
        by_cases hout : eulerMonomialOutput k col j = row
        · rw [ite_eq_left hout]
          have hz : eulerMonomialWeight k col j = 0 := by
            by_contra hj
            exact hji (show j = i by
                apply eulerLowExponent_injective (k + 2)
                have h₀ := congrArg Prod.fst (hout.trans hrow.symm)
                have h₁ := congrArg Prod.snd (hout.trans hrow.symm)
                ext t
                rcases col with c | c | c
                · change (eulerLowExponent k c 1 : ℤ) - eulerLowExponent (k + 2) j 1 ≠ 0 at hj
                  change (eulerLowExponent k c 1 : ℤ) - eulerLowExponent (k + 2) i 1 ≠ 0 at hi
                  change eulerLowExponent k c 0 + eulerLowExponent (k + 2) j 0 =
                    eulerLowExponent k c 0 + eulerLowExponent (k + 2) i 0 at h₀
                  change eulerLowExponent k c 1 + eulerLowExponent (k + 2) j 1 - 1 =
                    eulerLowExponent k c 1 + eulerLowExponent (k + 2) i 1 - 1 at h₁
                  fin_cases t
                  · grind
                  grind
                · change (eulerLowExponent (k + 2) j 0 : ℤ) - eulerLowExponent k c 0 ≠ 0 at hj
                  change (eulerLowExponent (k + 2) i 0 : ℤ) - eulerLowExponent k c 0 ≠ 0 at hi
                  change eulerLowExponent k c 0 + eulerLowExponent (k + 2) j 0 - 1 =
                    eulerLowExponent k c 0 + eulerLowExponent (k + 2) i 0 - 1 at h₀
                  change eulerLowExponent k c 1 + eulerLowExponent (k + 2) j 1 =
                    eulerLowExponent k c 1 + eulerLowExponent (k + 2) i 1 at h₁
                  fin_cases t
                  · grind
                  grind
                · change eulerTopExponent k c 0 + eulerLowExponent (k + 2) j 0 =
                    eulerTopExponent k c 0 + eulerLowExponent (k + 2) i 0 at h₀
                  change eulerTopExponent k c 1 + eulerLowExponent (k + 2) j 1 =
                    eulerTopExponent k c 1 + eulerLowExponent (k + 2) i 1 at h₁
                  fin_cases t
                  · grind
                  grind)
          grind
        grind
      · simp
    · left
      apply Finset.sum_eq_zero
      grind [eulerClosedForm_monomial_entry]
  · rw [hz, map_zero, l1Norm_zero]
    grind
  · rw [hm, map_mul, eval₂Hom_C]
    have hX : eval₂Hom (Int.castRingHom (MvPolynomial σ ℤ))
        (eulerCoefficientData (k + 2) f) (X i) = eulerCoefficientData (k + 2) f i :=
      eval₂_X _ _ _
    rw [hX]
    change l1Norm (C c * eulerCoefficientData (k + 2) f i) ≤ _
    apply (l1Norm_mul_le _ _).trans
    rw [l1Norm_C]
    apply Nat.mul_le_mul _ (hcoeff i)
    grind

/-- For a monomial of degree `k + 2`, every Euler matrix entry of its universal plane restriction
has coefficient ℓ¹-norm at most `(k + 2) * 3 ^ (k + 2)`. -/
theorem ambientEulerEntry_monomial_l1_le (k : ℕ)
    (m : σ →₀ ℕ) (hm : m.degree = k + 2) (row : ℕ × ℕ) (col : EulerColumns k) :
    l1Norm (ambientEulerEntryLinear ℤ σ k row col (monomial m 1)) ≤
      (k + 2) * 3 ^ (k + 2) := by
  rw [ambientEulerEntryLinear_apply]
  apply eulerClosedForm_entry_l1_le k (3 ^ (k + 2)) _
  · exact (universalPlanePolynomial_totalDegree_le _).trans
      ((totalDegree_monomial_le m (1 : ℤ)).trans (by change m.degree ≤ k + 2; omega))
  · intro i
    simpa [eulerCoefficientData, universalPlanePolynomial,
      AlgEquiv.symm_apply_apply, hm] using
      (l1Norm_coeff_le_l1Norm_sumAlgEquiv_symm _ ((Finsupp.degreeLeEquivSym (Fin 2) (k + 2)).symm i).val).trans (show l1Norm ((sumAlgEquiv ℤ (Fin 2) (PlaneParameters σ)).symm
            (universalPlaneMap ℤ σ (monomial m 1))) ≤ 3 ^ m.degree by
          rw [universalPlaneMap, aeval_monomial, map_one, one_mul]
          change l1Norm ((sumAlgEquiv ℤ (Fin 2) (PlaneParameters σ)).symm
            (∏ i ∈ m.support,
              (C (X (i,0)) + C (X (i,1)) * X 0 + C (X (i,2)) * X 1) ^ m i)) ≤ _
          rw [map_prod]
          simp only [map_pow]
          calc
            _ ≤ ∏ i ∈ m.support, l1Norm
                (((sumAlgEquiv ℤ (Fin 2) (PlaneParameters σ)).symm
                  (C (X (i,0)) + C (X (i,1)) * X 0 + C (X (i,2)) * X 1)) ^ m i) :=
              l1Norm_prod_le _ _
            _ ≤ ∏ i ∈ m.support, 3 ^ m i :=
              Finset.prod_le_prod fun i _ =>
                (l1Norm_pow_le _ _).trans
                  (Nat.pow_le_pow_left (show l1Norm ((sumAlgEquiv ℤ (Fin 2) (PlaneParameters σ)).symm
                        (C (X (i,0)) + C (X (i,1)) * X 0 + C (X (i,2)) * X 1)) ≤ 3 by
                      simp
                      have hx (j : Fin 2 ⊕ PlaneParameters σ) :
                          l1Norm (X j : MvPolynomial (Fin 2 ⊕ PlaneParameters σ) ℤ) = 1 := by
                        simp [X]
                      apply (l1Norm_add_le _ _).trans
                      have hab := (l1Norm_add_le
                        (X (Sum.inr (i,0)) : MvPolynomial (Fin 2 ⊕ PlaneParameters σ) ℤ)
                          (X (Sum.inr (i,1)) * X (Sum.inl 0))).trans
                          (Nat.add_le_add_left (l1Norm_mul_le _ _) _)
                      have hc := l1Norm_mul_le
                        (X (Sum.inr (i,2)) : MvPolynomial (Fin 2 ⊕ PlaneParameters σ) ℤ) (X (Sum.inl 1))
                      simpa [hx] using Nat.add_le_add hab hc) _)
            _ = 3 ^ m.degree := by
              rw [Finset.prod_pow_eq_pow_sum]
              rfl)

