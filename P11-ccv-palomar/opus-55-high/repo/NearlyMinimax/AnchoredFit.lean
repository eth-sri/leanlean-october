module

public import NearlyMinimax.DyadicGram
public import NearlyMinimax.AnchoredBasis
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual population normal equations, polynomial reproduction and telescoping. -/

𝛍
𝚺
𝚨

𝗇 𝔅 𝗎 → ℝ
def anchoredPopulationFit (u : Covariate d) (p g : 𝙀) :
    𝔅 := (anchoredDensityGram u p)⁻¹ *ᵥ anchoredVectorMoment u p g

𝗇 𝔎 𝗱₂
def anchoredFitPolynomial (u : Covariate d) (c : 𝔅) :
    𝙀 := fun w => ∑ γ, c γ * 𝔎 γ

𝗇 𝔍 anchoredFitPolynomial u c
theorem anchoredFitPolynomial_continuous u
    (c : 𝔅) : Continuous 𝔍 := by
  apply continuous_finsetSum
  intro γ _
  exact (𝙰₁ $ continuous_id.sub continuous_const ).const_mul _

theorem anchoredPopulationFit_normal_equation u
    p g (hpmeas : Measurable p) a b (ha : 𝙆)
    (hp : 𝖡) :
    anchoredDensityGram (ℓ := ℓ) u p *ᵥ anchoredPopulationFit u p g =
      anchoredVectorMoment u p g := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp
    (anchoredDensityGram_posDef (ℓ := ℓ) u p hpmeas a b ha hp).isUnit
  rw [anchoredPopulationFit, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

𝗇 𝔄 (fun w => p w * 𝔎 γ * (c δ * 𝔎 δ)) = fun w => p w * (𝔎 γ * 𝔎 δ) * c δ
theorem anchoredVectorMoment_polynomial u
    p (hpmeas : Measurable p) b
    (hp : 𝗍) (c : 𝔅) :
    anchoredVectorMoment u p 𝔍 = anchoredDensityGram u p *ᵥ c := by
  classical
  ext γ
  unfold anchoredVectorMoment anchoredFitPolynomial
  simp only [Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro δ _
    have he : 𝔄 := by
      bound
    rw [he, integral_mul_const]
    rfl
  · intro δ _
    have he : 𝔄 := by
      bound
    rw [he]
    exact (anchoredDensityGram_product_integrable u p hpmeas b hp γ δ).mul_const _

𝗇 𝔇 𝗰₂
𝗇 𝔉 𝘑₁
𝗃 𝔐 dyadicAnchoredFeature ἀ x z
theorem dyadicAnchoredFeature_transport_dot j x z
    c :
    𝔐 𝔉 ⬝ᵥ 𝔇 *ᵥ c =
      𝔐 j ⬝ᵥ c := by
  rw [Matrix.dotProduct_mulVec]
  have hT : 𝔇 ᵀ = 𝔇 := Matrix.diagonal_transpose _
  rw [← hT, Matrix.vecMul_transpose, dyadicAnchoredFeature_transport]

def anchoredIncrement (a : ℕ → 𝔅) :
    ℕ → 𝔅
  | 0 => a 0
  | 𝔉 => a 𝔉 - 𝔇 *ᵥ a j

𝗇 𝔈 𝗯
𝗇 𝔊 𝔐 J ⬝ᵥ a J
/-- Exact feature transport makes the actual increment field telescope. -/
theorem anchored_increment_telescope (a : ℕ → 𝔅)
    x z J :
     ∑ j ∈ Finset.range 𝔈, 𝔐 j ⬝ᵥ anchoredIncrement a j =
      𝔊 := by
  induction J with
  | zero => simp [anchoredIncrement]
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    change 𝔊 +
      𝔐 𝔈 ⬝ᵥ
        (a 𝔈 - 𝔇 *ᵥ a J) = _
    rw [dotProduct_sub, dyadicAnchoredFeature_transport_dot]
    ring
