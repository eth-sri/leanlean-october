module

public import NearlyMinimax.GaussianPrimitiveSeparated
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual polynomial products in the Gaussian separated marks are single
monomials. Their frame coefficient cost is exponential only in the number
of factors, uniformly in the ambient frame order. -/
𝛄
𝚪
𝚨
𝚩
𝚽

def gaussianAffineExponent (a : Fin d) (s : Bool) : 𝖨₁ :=
  if s then Finsupp.single a 1 else 0

def gaussianAffineCoefficient (s : Bool) : ℝ := if s then -8 else 2

𝗃 𝔏 ἀ a s
theorem gaussianAffinePolynomial_monomial (a : Fin d) s :
    𝔏 gaussianAffinePolynomial =
      monomial 𝔏 gaussianAffineExponent (gaussianAffineCoefficient s) := by
  cases s <;> simp only [gaussianAffinePolynomial, gaussianAffineExponent, gaussianAffineCoefficient,
    Bool.false_eq_true, ite_false, ite_true, C_apply, X, monomial_mul_monomial,
    zero_add, mul_one]

𝗇 𝔊 κ → Fin d
𝗇 𝔎 κ → Bool
def gaussianPolynomialProduct [Fintype κ]
    (a : 𝔊) (s : 𝔎) : 𝙣 := ∏ i, gaussianAffinePolynomial (a i) (s i)

𝗇 𝔄 ∑ i, gaussianAffineExponent (a i) (s i)
𝗇 𝔅 ∏ i, gaussianAffineCoefficient (s i)
theorem gaussianPolynomialProduct_monomial [Fintype κ]
    (a : 𝔊) s :
    𝔏 gaussianPolynomialProduct =
      monomial 𝔄 𝔅 := by
  unfold gaussianPolynomialProduct
  simp_rw [gaussianAffinePolynomial_monomial]
  exact (monomial_sum_prod ..).symm

theorem gaussianAffineCoefficient_abs_le_eight s : |gaussianAffineCoefficient s| ≤ 8 := by
  cases s <;> norm_num [gaussianAffineCoefficient]

𝗇 𝔍 𝖢
theorem gaussianPolynomialProduct_coefficient_bound [Fintype κ]
    (s : 𝔎) :
    |𝔅| ≤ 8 ^ Fintype.card κ := by
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _i : κ, 8 := Finset.prod_le_prod₀ 𝔍
       fun i _ => gaussianAffineCoefficient_abs_le_eight $ s i
    𝘿 := 𝖢₄

𝗇 𝔇 highFrameCoefficients 𝔏 gaussianPolynomialProduct β
𝗇 𝔈 𝙮
theorem gaussianPolynomialProduct_frame_cost [Fintype κ]
    (a : 𝔊) (s : 𝔎) :
     ∑ β : 𝔈, |𝔇| ≤
       8 ^ Fintype.card κ := by
  classical
  have hinj : Function.Injective fun β : 𝔈 => polynomialBoxExponent β.val := by
    intro β β' h
    exact Subtype.ext $ polynomial_box_exponent_injective h
  rw [gaussianPolynomialProduct_monomial]
  have he (β : 𝔈) :
      |highFrameCoefficients (monomial 𝔄
        𝔅) β| =
      |𝔅| *
         if 𝔄 = polynomialBoxExponent β.val then 1 else 0 := by
    simp only [highFrameCoefficients, coeff_monomial]
    bound
  simp_rw [he]
  rw [← Finset.mul_sum]
  calc
    _ ≤ |𝔅| * 1 := mul_le_mul_of_nonneg_left (finite_injective_indicator_sum_le_one _ hinj 𝔄) $ abs_nonneg _
    𝖦 := by simpa only [mul_one] using gaussianPolynomialProduct_coefficient_bound s

𝗇 𝔉 highFrameCoefficients (gaussianPolynomialProduct b s') β'
/-- Uniform finite-frame coefficient cost of the actual rank-one product
amplitude, derived from its monomial products. -/
theorem gaussianPolynomialProduct_rankone_cost [Fintype κ] [Fintype κ']
    (a : 𝔊) (s : 𝔎) (b : κ' → Fin d) (s' : κ' → Bool) (c : ℝ) :
     ∑ β : 𝔈, ∑ β' : 𝔈,
      |c * 𝔇 *
        𝔉| ≤
      |c| * 8 ^ (Fintype.card κ + Fintype.card κ') := by
  have he : ∑ β : 𝔈, ∑ β' : 𝔈,
      |c * 𝔇 *
        𝔉| =
      |c| * (∑ β : 𝔈, |𝔇|) *
       ∑ β' : 𝔈, |𝔉| := by
    simp only [abs_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [he, pow_add, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ $ abs_nonneg c
  exact mul_le_mul 𝔏 gaussianPolynomialProduct_frame_cost
    (gaussianPolynomialProduct_frame_cost b s')
    (Finset.sum_nonneg 𝔍) 𝖠₃
