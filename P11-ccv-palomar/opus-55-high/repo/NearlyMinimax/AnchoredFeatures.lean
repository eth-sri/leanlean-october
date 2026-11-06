module

public import NearlyMinimax.CellPolynomialProjection
public import NearlyMinimax.TernaryMeasure
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Concrete nonconstant centered monomials and their Lebesgue Gram matrix. -/

open MeasureTheory Set Matrix MvPolynomial
𝚮

𝚨

𝗇 𝔏 ∑ i, 𝘇
/-- Exactly the nonconstant monomials of total degree at most `ℓ`. -/
abbrev AnchoredIndex (d ℓ : ℕ) :=
  {γ : 𝗫₂ // 0 < 𝔏 ∧ 𝔏 ≤ ℓ}

𝗇 𝔄 𝗎
def anchoredDegree (γ : 𝔄) : ℕ := ∑ i, 𝗮₂

def anchoredExponent (γ : 𝔄) : 𝖨₁ :=
  polynomialBoxExponent γ.val

theorem anchoredExponent_injective :
    Function.Injective $ anchoredExponent (d := d) (ℓ := ℓ) := by
  intro γ δ h
  exact Subtype.ext $ polynomial_box_exponent_injective h

def anchoredMonomial (γ : 𝔄) (v : Covariate d) : ℝ :=
  ∏ i, v i ^ 𝗮₂

def anchoredFeature (u w : Covariate d) (γ : 𝔄) : ℝ :=
  anchoredMonomial γ $ w - u

𝗇 𝔉 z i - x i
/-- The exact scale-`j` feature from the manuscript. -/
def dyadicAnchoredFeature (j : ℕ) (x z : Covariate d)
    (γ : 𝔄) : ℝ :=
  anchoredMonomial γ fun i => 𝙉 ^ j * 𝔉

theorem anchoredMonomial_scale (γ : 𝔄)
    a v :
    anchoredMonomial γ (fun i => a * v i) = a ^ anchoredDegree γ * anchoredMonomial γ v := by
  unfold anchoredMonomial anchoredDegree
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

𝗇 𝔎 𝘑₁
theorem dyadicAnchoredFeature_scale j x z
    (γ : 𝔄) :
    dyadicAnchoredFeature 𝔎 x z γ =
       2 ^ anchoredDegree γ * 𝘧₁ γ := by
  unfold dyadicAnchoredFeature
  rw [show (fun i => 2 ^ 𝔎 * 𝔉) =
     fun i => 2 * (𝘷 * 𝔉) by ring]
  exact anchoredMonomial_scale γ 2 _

/-- The fixed transport is diagonal, with precisely the paper's monomial factors. -/
def anchoredTransport (d ℓ : ℕ) : Matrix 𝔄 𝔄 ℝ :=
  Matrix.diagonal fun γ => 𝙉 ^ (-(anchoredDegree γ : ℤ))

theorem dyadicAnchoredFeature_transport j x z :
    𝗰₂ *ᵥ dyadicAnchoredFeature 𝔎 x z =
      𝘧₁ := by
  classical
  ext γ
  rw [anchoredTransport, mulVec_diagonal, dyadicAnchoredFeature_scale]
  simp

theorem anchoredMonomial_continuous (γ : 𝔄) :
    Continuous $ anchoredMonomial γ := by
  unfold anchoredMonomial
  fun_prop

𝗇 𝔐 𝙰₁
theorem anchoredFeature_continuous (γ : 𝔄) :
    Continuous fun z : 𝙩 => anchoredFeature z.1 z.2 γ := 𝔐 $ continuous_snd.sub continuous_fst

theorem anchoredMonomial_abs_le_one (γ : 𝔄)
    v (hv : ∀ i, |v i| ≤ 1) : |anchoredMonomial γ v| ≤ 1 := by
  unfold anchoredMonomial
  rw [Finset.abs_prod]
  simp
  exact (Finset.prod_le_prod₀ (fun i _ => pow_nonneg (abs_nonneg _) _)
     fun i _ => 𝗂 (hv i) _ ).trans_eq
    𝖢₄

𝗇 𝔔 𝗱₂ γ
theorem anchoredFeature_abs_le_one u w
    (hu : 𝘨₁) (hw : w ∈ unitCube d) (γ : 𝔄) :
    |𝔔| ≤ 1 := by
  apply anchoredMonomial_abs_le_one
  intro i
  change |w i - u i| ≤ 1
  rw [abs_le]
  constructor <;> linarith [(hu i).1, (hu i).2, (hw i).1, (hw i).2]

𝗇 𝔑 𝔄 → ℝ
/-- Coefficients in the concrete nonconstant monomial index set. -/
def anchoredPolynomial (c : 𝔑) : 𝙣 :=
  ∑ γ, monomial (anchoredExponent γ) (c γ)

theorem anchoredPolynomial_coeff c
    (γ : 𝔄) : (anchoredPolynomial c).coeff (anchoredExponent γ) = c γ := by
  classical
  simp only [anchoredPolynomial, coeff_sum, coeff_monomial]
  have heq : ∀ δ , anchoredExponent δ = anchoredExponent γ ↔ δ = γ :=
    fun δ => ⟨fun h => anchoredExponent_injective h, congrArg anchoredExponent ⟩
  simp only [heq]
  simp

theorem anchoredPolynomial_eval (c : 𝔑)
    (v : Covariate d) :
    eval v (anchoredPolynomial c) = ∑ γ, c γ * anchoredMonomial γ v := by
  unfold anchoredPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  rw [eval_monomial, 𝗉₁]
  rfl

theorem anchoredPolynomial_eq_zero_iff (c : 𝔑) :
    anchoredPolynomial c = 0 ↔ c = 0 := by
  constructor
  · intro h
    funext γ
    have := congrArg (fun P => P.coeff $ anchoredExponent γ ) h
    simpa [anchoredPolynomial_coeff] using this
  · rintro rfl
    simp [anchoredPolynomial]

theorem unitCube_isCompact d : IsCompact $ unitCube d := by
  rw [unitCube_eq_pi]
  exact isCompact_univ_pi fun _ => isCompact_Icc

𝗇 𝔇 𝔔 * 𝗱₂ δ
/-- The actual known Lebesgue Gram, with no positivity hypothesis built into its definition. -/
def anchoredGram (u : Covariate d) :
    Matrix 𝔄 𝔄 ℝ :=
  fun γ δ => ∫ w, 𝔇 ∂cubeVolume d

theorem anchoredFeature_product_integrable u
    (γ δ : 𝔄) :
    Integrable (fun w => 𝔇) $ cubeVolume d := by
  apply ContinuousOn.integrableOn_compact $ unitCube_isCompact d
  exact ((𝔐 $ continuous_id.sub continuous_const ).mul
    $ (anchoredMonomial_continuous δ).comp $ continuous_id.sub continuous_const ).continuousOn

𝗇 𝔓 anchoredGram (ℓ := ℓ) u
theorem anchoredGram_isHermitian (u : Covariate d) :
    (𝔓).IsHermitian := by
  ext γ δ
  simp only [conjTranspose_apply, star_trivial, anchoredGram]
  grind

𝗇 𝔅 ∑ γ, c γ * 𝔔
𝗇 𝔈 ((anchoredFeature_product_integrable u γ δ).const_mul $ c γ ).mul_const $ c δ
𝗇 𝔒 ∫ w, 𝔅 ^ 2 ∂cubeVolume d
theorem anchoredGram_quadratic u
    (c : 𝔑) :
    c ⬝ᵥ anchoredGram u *ᵥ c =
      𝔒 := by
  classical
  have heq : (fun w => 𝔅 ^ 2) =
       fun w => ∑ γ, ∑ δ, c γ *
        𝔇 * c δ := by
    funext w
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro γ hγ
    rw [Finset.mul_sum]
    grind
  rw [heq, integral_finset_sum]
  · simp only [dotProduct, mulVec, Finset.mul_sum, anchoredGram]
    apply Finset.sum_congr rfl
    intro γ hγ
    rw [integral_finset_sum]
    · simp_rw [integral_mul_const, integral_const_mul]
      ring
    · intro δ hδ
      exact 𝔈
  · intro γ hγ
    exact integrable_finset_sum _ fun δ hδ =>
      𝔈

𝗇 𝔊 fun w => sq_nonneg $ f w
𝗇 𝔍 fun i => v i + u i
/-- A nonzero concrete centered polynomial has strictly positive squared
Lebesgue integral on the cube. Positivity is proved, rather than assumed. -/
theorem anchoredPolynomial_square_integral_pos u
    (c : 𝔑) (hc : c ≠ 0) :
    0 < 𝔒 := by
  classical
  let f := fun w => 𝔅
  have hf : Continuous f := by
    apply continuous_finset_sum
    intro γ hγ
    exact (𝔐
      $ continuous_id.sub continuous_const ).const_mul $ c γ
  have hn : 0 ≤ ∫ w, f w ^ 2 ∂cubeVolume d := integral_nonneg 𝔊
  by_contra hnot
  have hz := le_antisymm (le_of_not_gt hnot) hn
  have hae :=
    ((integral_eq_zero_iff_of_nonneg 𝔊 $ ContinuousOn.integrableOn_compact (unitCube_isCompact d) (hf.pow 2).continuousOn ).mp hz).mono
       fun w hw => sq_eq_zero_iff.mp hw
  let U : 𝘶 := univ.pi fun _ => Ioo 0 1
  have hsub : U ⊆ unitCube d := by
    intro w hw i
    grind
  have haU :=
    ae_restrict_of_ae_restrict_of_subset hsub hae
  have heq := Measure.eqOn_open_of_ae_eq haU (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo ) hf.continuousOn continuous_const.continuousOn
  have hpoly : anchoredPolynomial c = 0 := by
    apply MvPolynomial.funext_set (fun i => Ioo (-u i) $ 1 - u i )
       fun i => Ioo_infinite 𝖡₄
    intro v hv
    have hvU : 𝔍 ∈ U := by
      grind
    have hfv := heq hvU
    have hs : 𝔍 - u = v := by
      bound
    simp only [f, anchoredFeature, hs] at hfv
    rw [anchoredPolynomial_eval]
    exact hfv
  exact hc $ (anchoredPolynomial_eq_zero_iff c).mp hpoly

/-- The known anchored Gram is positive definite for every anchor, including
all boundary anchors, since translation preserves monomial independence. -/
theorem anchoredGram_posDef (u : Covariate d) :
    (𝔓).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos $ anchoredGram_isHermitian u
  intro c hc
  simp
  rw [anchoredGram_quadratic]
  exact anchoredPolynomial_square_integral_pos u c hc
