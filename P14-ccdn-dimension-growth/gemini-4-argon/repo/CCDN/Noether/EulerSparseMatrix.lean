/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.EulerUniversalForms
import CCDN.Noether.EulerMonomialColumns
import CCDN.Noether.EulerPairSpecialization
import CCDN.Noether.ShearNormalization

/-! Each row and Euler column uses at most one coefficient of the defining
equation, with integer multiplier bounded by its degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

/-- An entry is zero or a single coefficient variable with multiplier
of absolute value at most the defining equation's degree. -/
theorem universalEulerMatrix_sparse (k : ℕ) (row : ℕ × ℕ) (col : EulerColumns k) :
    universalEulerMatrix k row col = 0 ∨
      ∃ (i : EulerLowIndex (k + 2)) (c : ℤ), |c| ≤ (k + 2 : ℕ) ∧
        universalEulerMatrix k row col = MvPolynomial.C c * MvPolynomial.X i := by
  classical
  let low (m : ℕ) (i : EulerLowIndex m) : Fin 2 →₀ ℕ :=
    ((Finsupp.degreeLeEquivSym (Fin 2) m).symm i).val
  let top (i : EulerTopIndex k) : Fin 2 →₀ ℕ :=
    ((degreeEqEquivSym (Fin 2) k).symm i).val
  have hlow (m : ℕ) (i : EulerLowIndex m) : low m i 0 + low m i 1 ≤ m := by
    have hh := ((Finsupp.degreeLeEquivSym (Fin 2) m).symm i).property
    change (low m i).sum (fun _ e => e) ≤ m at hh
    rwa [bivariate_exponent_eq (low m i), bivariate_exponent_sum] at hh
  have htop (i : EulerTopIndex k) : top i 0 + top i 1 = k := by
    have hh := ((degreeEqEquivSym (Fin 2) k).symm i).property
    change (top i).sum (fun _ e => e) = k at hh
    rwa [bivariate_exponent_eq (top i), bivariate_exponent_sum] at hh
  let out (i : EulerLowIndex (k + 2)) : ℕ × ℕ :=
    let s := low (k + 2) i 0
    let t := low (k + 2) i 1
    match col with
    | .inl j => (low k j 0 + s, low k j 1 + t - 1)
    | .inr (.inl j) => (low k j 0 + s - 1, low k j 1 + t)
    | .inr (.inr j) => (top j 0 + s, top j 1 + t)
  let wt (i : EulerLowIndex (k + 2)) : ℤ :=
    let s := low (k + 2) i 0
    let t := low (k + 2) i 1
    match col with
    | .inl j => (low k j 1 : ℤ) - t
    | .inr (.inl j) => (s : ℤ) - low k j 0
    | .inr (.inr _) => (k + 2 : ℕ) - (s : ℤ) - t
  have hentry (i : EulerLowIndex (k + 2)) :
      eulerClosedFormCoefficientMatrix k (eulerCoefficientMonomial ℤ (k + 2) i) row col =
        if out i = row then wt i else 0 := by
    have hout : eulerClosedFormOperator k (eulerCoefficientMonomial ℤ (k + 2) i)
        (eulerPairBasis ℤ k col) =
        monomial (out i).1 (monomial (out i).2 (wt i)) := by
      change closedFormOperator _ (eulerBivariatePair ℤ k (eulerPairBasis ℤ k col)) = _
      rw [show eulerCoefficientMonomial ℤ (k + 2) i =
          monomial (low (k + 2) i 0) (monomial (low (k + 2) i 1) (1 : ℤ)) from
        bivariatePolynomialEquiv_monomial _ _]
      rcases col with j | j | j
      · simp only [eulerBivariatePair, LinearMap.comp_apply, LinearMap.prodMap_apply,
          AlgEquiv.toLinearMap_apply, eulerPairCoordinates_basis_left,
          bivariatePolynomialEquiv_monomial, map_zero]
        exact closedFormOperator_monomial_left _ _ _ _
      · simp only [eulerBivariatePair, LinearMap.comp_apply, LinearMap.prodMap_apply,
          AlgEquiv.toLinearMap_apply, eulerPairCoordinates_basis_right,
          bivariatePolynomialEquiv_monomial, map_zero]
        exact closedFormOperator_monomial_right _ _ _ _
      · simp only [eulerBivariatePair, LinearMap.comp_apply, LinearMap.prodMap_apply,
          AlgEquiv.toLinearMap_apply, eulerPairCoordinates_basis_radial, map_mul, map_neg,
          bivariatePolynomialEquiv_monomial, bivariatePolynomialEquiv_X_zero,
          bivariatePolynomialEquiv_X_one, C_mul_monomial, X_mul_monomial]
        change closedFormOperator _
          (monomial (top j 0) (monomial (top j 1 + 1) (1 : ℤ)),
           -(monomial (top j 0 + 1) (monomial (top j 1) (1 : ℤ)))) = _
        rw [closedFormOperator_monomial_radial, htop]
    change ((eulerClosedFormOperator k (eulerCoefficientMonomial ℤ (k + 2) i)
      (eulerPairBasis ℤ k col)).coeff row.1).coeff row.2 = _
    rw [hout]
    by_cases h₀ : (out i).1 = row.1 <;>
      by_cases h₁ : (out i).2 = row.2 <;>
      simp [coeff_monomial, Prod.ext_iff, h₀, h₁]
  have hinj_exp : Function.Injective (low (k + 2)) :=
    Subtype.val_injective.comp (Finsupp.degreeLeEquivSym (Fin 2) (k + 2)).symm.injective
  have hinj (i j : EulerLowIndex (k + 2))
      (hi : wt i ≠ 0) (hj : wt j ≠ 0) (he : out i = out j) : i = j := by
    apply hinj_exp
    have h₀ := congrArg Prod.fst he
    have h₁ := congrArg Prod.snd he
    ext t
    rcases col with c | c | c <;>
      dsimp only [wt, out] at hi hj h₀ h₁ <;>
      (fin_cases t <;> dsimp only [Fin.zero_eta, Fin.mk_one] <;> omega)
  by_cases hex : ∃ i, wt i ≠ 0 ∧ out i = row
  · obtain ⟨i, hi, hrow⟩ := hex
    have habs : |wt i| ≤ (k + 2 : ℕ) := by
      have hid := hlow (k + 2) i
      rcases col with j | j | j
      · have := hlow k j
        change |(low k j 1 : ℤ) - low (k + 2) i 1| ≤ _
        rw [abs_le]; constructor <;> omega
      · have := hlow k j
        change |(low (k + 2) i 0 : ℤ) - low k j 0| ≤ _
        rw [abs_le]; constructor <;> omega
      · change |((k + 2 : ℕ) : ℤ) - low (k + 2) i 0 - low (k + 2) i 1| ≤ _
        rw [abs_le]; constructor <;> omega
    refine Or.inr ⟨i, wt i, habs, ?_⟩
    unfold universalEulerMatrix
    rw [Finset.sum_eq_single i]
    · rw [hentry, ite_eq_left hrow]
    · intro j _ hji
      rw [hentry]
      split_ifs with hout
      · rw [show wt j = 0 by
          by_contra hj; exact hji (hinj j i hj hi (hout.trans hrow.symm)), map_zero, zero_mul]
      · simp
    · simp
  · refine Or.inl (Finset.sum_eq_zero fun i _ => ?_)
    rw [hentry]
    split_ifs with hout
    · rw [show wt i = 0 by by_contra hi; exact hex ⟨i, hi, hout⟩,
        map_zero, zero_mul]
    · simp

end
end CCDN
