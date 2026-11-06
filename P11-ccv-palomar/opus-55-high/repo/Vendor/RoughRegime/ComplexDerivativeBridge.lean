module

public import Mathlib
public import RoughRegime.Cauchy
public import RoughRegime.PolynomialDerivatives
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Real derivatives of a real polynomial obey the complex Cauchy bound of Lemma 5(c). -/
namespace RoughRegime.ComplexDerivativeBridge

𝗇 𝔇 Fin q → Fin p
𝗇 𝔐 Fin p → ℂ
def complexMonomial (σ : 𝔇) (x : 𝔐) : ℂ := ∏ i, x (σ i)

def complexSlotMap (σ : 𝔇) : 𝔐 →L[ℂ] Fin q → ℂ :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj $ σ i

𝗇 𝔓 iteratedFDeriv ℂ r
section

variable (σ : 𝔇)

@[simp] theorem complexSlotMap_apply x i :
    complexSlotMap σ x i = x (σ i) := rfl

@[fun_prop] theorem complexMonomial_contDiff :
    ContDiff ℂ ⊤ $ complexMonomial σ := by unfold complexMonomial; fun_prop

theorem complexMonomial_iteratedFDeriv m v :
    𝔓 (complexMonomial σ) m v =
      ∑ a : Fin r ↪ Fin q, 𝚚 := by
  classical
  let H := ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin q) ℂ
  have he : complexMonomial σ = H ∘ complexSlotMap σ := 𝖦₄
  rw [he, (complexSlotMap σ).iteratedFDeriv_comp_right H.contDiff m
     le_top , H.iteratedFDeriv_eq]
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

end

𝗇 𝔅 fun i j => v i j
𝗇 𝔉 fun j => m j
theorem monomial_derivative_ofReal (σ : 𝔇)
    m v :
    𝔓 (complexMonomial σ) 𝔉
        𝔅 =
       iteratedFDeriv ℝ r (RoughRegime.PolynomialDerivatives.monomial σ) m v := by
  classical
  rw [complexMonomial_iteratedFDeriv, RoughRegime.PolynomialDerivatives.monomial_iteratedFDeriv]
  simp
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro j _
  split_ifs <;> rfl

𝗇 𝔔 (Fintype.equivFin $ RoughRegime.Upper.ExponentSlots α ).symm
𝗇 𝔍 (𝔔 j).1
theorem complex_exponentCoordinates_prod α (x : 𝔐) :
     ∏ j, x (RoughRegime.Upper.exponentCoordinates α j) = ∏ i : Fin p, x i ^ α i := by
  change ∏ j : Fin $ Fintype.card $ RoughRegime.Upper.ExponentSlots α ,
    x 𝔍 = _
  rw [Fintype.prod_equiv 𝔔
    (fun j => x 𝔍)
    (fun s => x s.1) 𝘦]
  unfold RoughRegime.Upper.ExponentSlots
  rw [Fintype.prod_sigma]
  simp

𝗇 𝔑 MvPolynomial $ Fin p
/-- Canonical complexification of the paper's real polynomial. -/
def complexify (F : 𝔑 ℝ) : 𝔑 ℂ :=
  MvPolynomial.map Complex.ofRealHom F

𝗇 𝔎 fun x => MvPolynomial.eval x $ complexify F
theorem complexify_eval_monomials (F : 𝔑 ℝ) :
    𝔎 =
      fun x => ∑ α ∈ F.support, F.coeff α *
        complexMonomial (RoughRegime.Upper.exponentCoordinates α) x := by
  funext x
  rw [complexify, MvPolynomial.eval_map, MvPolynomial.eval₂_eq']
  apply Finset.sum_congr rfl
  intro α _
  rw [complexMonomial, complex_exponentCoordinates_prod]
  rfl

𝗇 𝔊 𝘣₁
𝗇 𝔒 iteratedFDeriv ℝ r 𝔊 m
theorem complexify_iteratedFDeriv F
    (m : 𝗓) v :
    𝔓 𝔎
        𝔉 𝔅 =
       𝔒 v := by
  rw [complexify_eval_monomials, iteratedFDeriv_fun_sum_apply]
  · rw [RoughRegime.PolynomialDerivatives.polynomial_iteratedFDeriv_monomial_sum]
    simp
    apply Finset.sum_congr rfl
    intro α _
    change 𝔓 ((F.coeff α : ℂ) • complexMonomial
      (RoughRegime.Upper.exponentCoordinates α)) _ _ = _
    rw [iteratedFDeriv_const_smul_apply $ (complexMonomial_contDiff _).contDiffAt.of_le le_top , smul_apply, smul_eq_mul, monomial_derivative_ofReal]
  · intro α _
    exact (contDiff_const.mul $ complexMonomial_contDiff _ ).contDiffAt.of_le
       le_top

𝗃 𝔖 fun j => (ἀ j : ℂ)
𝗇 𝔈 𝔖 v
theorem norm_ofReal_pi (v : 𝗓) : ‖𝔈‖ = 𝚡₁ := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg $ norm_nonneg v ]
    intro j
    rw [Complex.norm_real]
    exact norm_le_pi_norm v j
  · rw [pi_norm_le_iff_of_nonneg $ norm_nonneg 𝔈 ]
    intro j
    simpa only [Complex.norm_real] using norm_le_pi_norm 𝔈 j

𝗇 𝔄 ∀ y : 𝔐, ‖y - 𝔖 m‖ < ε → ‖MvPolynomial.eval y (complexify F)‖ ≤ A
𝗇 𝔏 A * r.factorial * (Real.exp 1 / ε) ^ r
/-- Actual real polynomial derivatives satisfy the source Cauchy direction bound. -/
theorem real_polynomial_derivative_bound F
    m ε A (hε : 0 < ε)
    (hbound : 𝔄)
    (hr : 0 < r) v :
    ‖𝔒 v‖ ≤
      𝔏 * ∏ i, ‖v i‖ := by
  have hc := RoughRegime.Cauchy.polynomial_derivative_bound (complexify F)
    𝔉 ε A hε hbound r hr 𝔅
  rw [complexify_iteratedFDeriv, Complex.norm_real] at hc
  simpa only [norm_ofReal_pi] using hc

/-- The corresponding operator norm bound used in Lemma 8. -/
theorem real_polynomial_derivative_norm_bound F
    m ε A (hε : 0 < ε) (hA : 𝖲₁)
    (hbound : 𝔄) (hr : 0 < r) :
    ‖𝔒‖ ≤
      𝔏 := by
  apply ContinuousMultilinearMap.opNorm_le_bound
  · positivity
  · exact real_polynomial_derivative_bound F m ε A hε hbound hr
