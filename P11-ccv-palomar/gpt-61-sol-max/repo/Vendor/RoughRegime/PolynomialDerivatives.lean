module

public import Mathlib
public import RoughRegime.Upper

@[expose] public section

/-! Exact Fréchet derivatives of monomials, including orders above the degree. -/

noncomputable section
open scoped BigOperators

namespace RoughRegime.PolynomialDerivatives

def monomial {p q } (σ : Fin q → Fin p) (x : Fin p → ℝ)  := ∏ i, x (σ i)

section
variable {p q : ℕ} (σ : Fin q → Fin p)
include σ

def slotMap  : (Fin p → ℝ) →L[ℝ] (Fin q → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (σ i))

@[simp] theorem slotMap_apply  x i :
    slotMap σ x i = x (σ i) := rfl
end


theorem monomial_iteratedFDeriv {p q r } σ
    (m : Fin p → ℝ) v :
    iteratedFDeriv ℝ r (monomial σ) m v =
      ∑ a : Fin r ↪ Fin q, ∏ j : Fin q,
        if h : j ∈ Set.range a then v (a.toEquivRange.symm ⟨j, h⟩) (σ j) else m (σ j) := by
  classical
  let H := ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin q) ℝ
  have he : monomial σ = H ∘ slotMap σ := by
    funext x
    simp [monomial, H]
  rw [he, (slotMap σ).iteratedFDeriv_comp_right H.contDiff m (show (r : WithTop ℕ∞) ≤ ⊤ from le_top),
    H.iteratedFDeriv_eq]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.iteratedFDeriv, sum_apply,
    ContinuousMultilinearMap.iteratedFDerivComponent_apply, H,
    ContinuousMultilinearMap.mkPiAlgebra_apply, slotMap_apply, Pi.compRightL_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro j _
  split_ifs with h
  · rcases h with ⟨k, rfl⟩
    simp
  · rfl

@[fun_prop] theorem monomial_contDiff {p q } (σ : Fin q → Fin p) :
    ContDiff ℝ ⊤ (monomial σ) := by
  unfold monomial
  fun_prop

section
variable {p q r : ℕ}

theorem monomial_iteratedFDeriv_above_degree  (σ : Fin q → Fin p)
    m v (hr : q < r) :
    iteratedFDeriv ℝ r (monomial σ) m v = 0 := by
  classical
  let : IsEmpty (Fin r ↪ Fin q) := ⟨fun a => by
    have hc := Fintype.card_le_of_injective a a.injective
    simp only [Fintype.card_fin] at hc
    omega⟩
  rw [monomial_iteratedFDeriv]
  exact Finset.sum_eq_zero (fun a _ => isEmptyElim a)

theorem monomial_derivative_const_mul  c (σ : Fin q → Fin p)
    m v :
    iteratedFDeriv ℝ r (fun x => c * monomial σ x) m v =
      c * iteratedFDeriv ℝ r (monomial σ) m v := by
  have hf : ContDiffAt ℝ r (monomial σ) m :=
    (monomial_contDiff σ).contDiffAt.of_le (show (r : WithTop ℕ∞) ≤ ⊤ from le_top)
  change (iteratedFDeriv ℝ r (c • monomial σ) m) v =
    (c • iteratedFDeriv ℝ r (monomial σ) m) v
  rw [iteratedFDeriv_const_smul_apply hf]
end


section
variable {p : ℕ} (F : MvPolynomial (Fin p) ℝ)

theorem polynomial_eq_monomials  :
    (fun x => MvPolynomial.eval x F) =
      fun x => ∑ α ∈ F.support, F.coeff α * monomial (Upper.exponentCoordinates α) x := by
  funext x
  rw [MvPolynomial.eval_eq']
  apply Finset.sum_congr rfl
  intro α _
  rw [monomial, Upper.exponentCoordinates_prod]

@[fun_prop] theorem polynomial_contDiff  :
    ContDiff ℝ ⊤ (fun x => MvPolynomial.eval x F) := by
  rw [polynomial_eq_monomials]
  fun_prop
end


theorem polynomial_iteratedFDeriv_monomial_sum {p r } F
    (m : Fin p → ℝ) v :
    iteratedFDeriv ℝ r (fun x => MvPolynomial.eval x F) m v =
      ∑ α ∈ F.support, F.coeff α *
        iteratedFDeriv ℝ r (monomial (Upper.exponentCoordinates α)) m v := by
  rw [polynomial_eq_monomials, iteratedFDeriv_fun_sum_apply]
  · simp only [sum_apply]
    solve_by_elim [Finset.sum_congr, monomial_derivative_const_mul]
  · intro α _
    exact (contDiff_const.mul (monomial_contDiff (Upper.exponentCoordinates α))).contDiffAt.of_le
      (show (r : WithTop ℕ∞) ≤ ⊤ from le_top)

end RoughRegime.PolynomialDerivatives
