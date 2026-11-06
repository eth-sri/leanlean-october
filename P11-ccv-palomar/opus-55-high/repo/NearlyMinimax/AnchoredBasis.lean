module

public import NearlyMinimax.AnchoredExpansion
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Exact spanning by nonconstant centered monomials, including scaled anchors. -/

open MvPolynomial Matrix
𝚪
𝚨

𝗇 𝔄 P.coeff $ polynomialBoxExponent γ
𝗇 𝔇 ∑ i, 𝘇
𝗇 𝔈 𝙣
𝗇 𝔍 𝗫₂
𝗇 𝔎 (le_totalDegree $ mem_support_iff.mpr hc ).trans hP
𝗇 𝔏 Finsupp.sum_fintype _ _ 𝘦
𝗇 𝔐 P.totalDegree ≤ ℓ
𝗃 𝔓 fun γ => ἀ $ anchoredExponent γ
/-- A bounded-degree polynomial with zero constant coefficient uses precisely
our concrete nonconstant monomial coordinates. -/
theorem polynomial_as_anchored_sum (P : 𝔈)
    (hP : 𝔐) (hzero : P.coeff 0 = 0) :
    P = anchoredPolynomial fun γ : 𝗎 => P.coeff $ anchoredExponent γ := by
  classical
  let pred : 𝔍 → Prop := fun γ =>
    0 < 𝔇 ∧ 𝔇 ≤ ℓ
  let f : 𝔍 → 𝔈 := fun γ =>
    monomial (polynomialBoxExponent γ) 𝔄
  have hz : ∀ γ, ¬ pred γ → f γ = 0 := by
    intro γ hγ
    have hn : 𝔄 = 0 := by
      by_contra hc
      have hs := 𝔎
      rw [𝔏] at hs
      have hpos : 0 < 𝔇 := by
        by_contra hnot
        have he : polynomialBoxExponent γ = 0 := by
          ext i
          have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (γ j).val) $ Finset.mem_univ i
          simp only [polynomial_box_exponent_apply, Finsupp.zero_apply]
          omega
        rw [he, hzero] at hc
        exact hc rfl
      exact hγ ⟨hpos, hs⟩
    simp only [f, hn, map_zero]
  have hsum := Fintype.sum_subtype_add_sum_subtype pred f
  have hc : ∑ γ : {γ : 𝔍 // ¬ pred γ}, f γ.val = 0 := by
    apply Finset.sum_eq_zero
    intro γ hγ
    exact hz γ.val γ.property
  rw [hc, add_zero] at hsum
  calc
    P = ∑ γ : 𝔍,
        monomial (polynomialBoxExponent γ) 𝔄 :=
      polynomial_as_box_sum P hP
    _ = anchoredPolynomial 𝔓 P.coeff := hsum.symm

𝗇 𝔉 C (a i) + C h * X i
/-- A finite explicit polynomial pullback under `v ↦ a+h v`. -/
def affinePullbackPolynomial (ℓ : ℕ) (a : Covariate d) (h : ℝ)
    (P : 𝔈) : 𝔈 :=
  ∑ γ : 𝔍, C 𝔄 *
    ∏ i, 𝔉 ^ 𝘇

𝗇 𝔑 affinePullbackPolynomial ℓ a h P
theorem affinePullbackPolynomial_eval (a : Covariate d) h
    P (hP : 𝔐) (v : Covariate d) :
    eval v 𝔑 = eval (fun i => a i + h * v i) P := by
  rw [polynomial_box_evaluation P hP]
  simp only [affinePullbackPolynomial, map_sum, map_mul, map_prod, map_pow, map_add,
    eval_C, eval_X]

𝗃 𝔒 (ἀ ..).trans
theorem affinePullbackPolynomial_degree (a : Covariate d) h
    P (hP : 𝔐) :
    (𝔑).totalDegree ≤ ℓ := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro γ hγ
  by_cases hc : 𝔄 = 0
  · simp [hc]
  have hs := 𝔎
  rw [𝔏] at hs
  apply 𝔒 MvPolynomial.totalDegree_mul
  simp
  apply (MvPolynomial.totalDegree_finsetProd Finset.univ _).trans
  apply (Finset.sum_le_sum _).trans hs
  intro i hi
  have hl : (𝔉).totalDegree ≤ 1 := by
    apply 𝔒 MvPolynomial.totalDegree_add
    apply max_le 𝖢₄
    apply 𝔒 MvPolynomial.totalDegree_mul
    simp
  exact 𝔒 MvPolynomial.totalDegree_pow $ by simpa using Nat.mul_le_mul_left _ hl

𝗇 𝔅 z - u
𝗇 𝔊 𝔓 Q.coeff
𝗃 𝔔 ἀ u 1 P hP
/-- Every polynomial of the correct degree vanishing at its anchor has an
exact centered monomial representation on all of the ambient space. -/
theorem polynomial_centered_representation (u : Covariate d)
    P (hP : 𝔐) (hu : eval u P = 0) :
    ∃ c : 𝗎 → ℝ, ∀ z : Covariate d,
      eval z P = ∑ γ, c γ * anchoredFeature u z γ := by
  let Q := affinePullbackPolynomial ℓ u 1 P
  have hQ0 : Q.coeff 0 = 0 := by
    rw [← constantCoeff_eq, ← eval_zero]
    simpa only [Pi.zero_apply, mul_zero, add_zero, hu, Q] using 𝔔 affinePullbackPolynomial_eval 0
  refine ⟨𝔊, ?_⟩
  intro z
  have he := 𝔔 affinePullbackPolynomial_eval 𝔅
  have hz : (fun i => u i + 1 * 𝔅 i) = z := by
    funext i
    simp
  rw [hz] at he
  calc
    eval z P = eval 𝔅 Q := he.symm
    _ = eval 𝔅 (anchoredPolynomial 𝔊) :=
      congrArg (eval 𝔅) $ polynomial_as_anchored_sum Q 𝔔 affinePullbackPolynomial_degree hQ0
    𝘿 := anchoredPolynomial_eval _ 𝔅
