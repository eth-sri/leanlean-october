module

public import Mathlib
public import RoughRegime.Upper
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Exact Fréchet derivatives of monomials, including orders above the degree. -/

𝚪

namespace RoughRegime.PolynomialDerivatives

𝗇 𝔄 Fin q → Fin p
𝗇 𝔈 𝗓
def monomial (σ : 𝔄) (x : 𝔈) : ℝ := ∏ i, x (σ i)

def slotMap (σ : 𝔄) : 𝔈 →L[ℝ] 𝚟₂ :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj $ σ i

@[simp] theorem slotMap_apply (σ : 𝔄) x i :
    slotMap σ x i = x (σ i) := rfl

𝗇 𝔅 iteratedFDeriv ℝ r (monomial σ) m
section

variable (σ : 𝔄)

include σ

𝗇 𝔉 Fin r ↪ Fin q
theorem monomial_iteratedFDeriv m v :
    𝔅 v =
      ∑ a : 𝔉, 𝚚 := by
  classical
  let H := ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin q) ℝ
  have he : monomial σ = H ∘ slotMap σ := by
    rfl
  rw [he, (slotMap σ).iteratedFDeriv_comp_right H.contDiff m le_top ,
    H.iteratedFDeriv_eq]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.iteratedFDeriv, sum_apply,
    ContinuousMultilinearMap.iteratedFDerivComponent_apply, H,
    ContinuousMultilinearMap.mkPiAlgebra_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro j _
  split_ifs with h
  · rcases h with ⟨k, rfl⟩
    simp
  · rfl

@[fun_prop] theorem monomial_contDiff :
    ContDiff ℝ ⊤ $ monomial σ := by
  unfold monomial
  fun_prop

theorem monomial_iteratedFDeriv_above_degree m v (hr : q < r) :
    𝔅 v = 0 := by
  classical
  let : IsEmpty 𝔉 := ⟨fun a => by
    have hc := Fintype.card_le_of_injective a a.injective
    simp at hc
    omega⟩
  rw [monomial_iteratedFDeriv]
  exact Finset.sum_eq_zero fun a _ => isEmptyElim a

end

𝗇 𝔊 iteratedFDeriv ℝ r
theorem monomial_derivative_const_mul c (σ : 𝔄)
    m v :
    𝔊 (fun x => c * monomial σ x) m v =
      c * 𝔅 v := by
  change (𝔊 (c • monomial σ) m) v =
    (c • 𝔅) v
  rw [iteratedFDeriv_const_smul_apply $ (monomial_contDiff σ).contDiffAt.of_le le_top ]

𝗇 𝔇 𝘣₁
𝗇 𝔍 monomial $ Upper.exponentCoordinates α
section

variable (F : 𝙩₁)

include F

theorem polynomial_eq_monomials :
    𝔇 =
      fun x => ∑ α ∈ F.support, F.coeff α * 𝔍 x := by
  funext x
  rw [MvPolynomial.eval_eq']
  apply Finset.sum_congr rfl
  intro α _
  rw [monomial, Upper.exponentCoordinates_prod]

@[fun_prop] theorem polynomial_contDiff :
    ContDiff ℝ ⊤ 𝔇 := by
  rw [polynomial_eq_monomials]
  fun_prop

end

theorem polynomial_iteratedFDeriv_monomial_sum F
    (m : 𝔈) v :
    𝔊 𝔇 m v =
      ∑ α ∈ F.support, F.coeff α *
        𝔊 𝔍 m v := by
  rw [polynomial_eq_monomials, iteratedFDeriv_fun_sum_apply]
  · simp
    apply Finset.sum_congr rfl
    intro α _
    exact monomial_derivative_const_mul ..
  · intro α _
    exact (contDiff_const.mul $ monomial_contDiff $ Upper.exponentCoordinates α ).contDiffAt.of_le
       le_top
