module

public import NearlyMinimax.DyadicGram
public import NearlyMinimax.AnchoredBasis

@[expose] public section

/-! Actual population normal equations, polynomial reproduction and telescoping. -/

noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

variable {d ℓ : ℕ} (u : Covariate d) (p g : Covariate d → ℝ) (c : AnchoredIndex d ℓ → ℝ)
    (a : ℕ → AnchoredIndex d ℓ → ℝ)

def anchoredPopulationFit :
    AnchoredIndex d ℓ → ℝ := (anchoredDensityGram u p)⁻¹ *ᵥ anchoredVectorMoment u p g

def anchoredFitPolynomial :
    Covariate d → ℝ := fun w => ∑ γ, c γ * anchoredFeature u w γ

theorem anchoredVectorMoment_polynomial
    {p : Covariate d → ℝ} (hpmeas : Measurable p) {b : ℝ}
    (hp : ∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b) (c : AnchoredIndex d ℓ → ℝ) :
    anchoredVectorMoment u p (anchoredFitPolynomial u c) = anchoredDensityGram u p *ᵥ c := by
  classical
  ext γ
  unfold anchoredVectorMoment anchoredFitPolynomial
  simp [Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro δ _
    have he : (fun w => p w * anchoredFeature u w γ * (c δ * anchoredFeature u w δ)) =
        fun w => (p w * (anchoredFeature u w γ * anchoredFeature u w δ)) * c δ := by
      funext w; ring
    rw [he, integral_mul_const]
    rfl
  · intro δ _
    have he : (fun w => p w * anchoredFeature u w γ * (c δ * anchoredFeature u w δ)) =
        fun w => (p w * (anchoredFeature u w γ * anchoredFeature u w δ)) * c δ := by
      funext w; ring
    rw [he]
    exact (anchoredDensityGram_product_integrable u hpmeas hp γ δ).mul_const _

theorem dyadicAnchoredFeature_transport_dot (j : ℕ) (x z : Covariate d)
    (c : AnchoredIndex d ℓ → ℝ) :
    dyadicAnchoredFeature (j + 1) x z ⬝ᵥ (anchoredTransport d ℓ *ᵥ c) =
      dyadicAnchoredFeature j x z ⬝ᵥ c := by
  rw [Matrix.dotProduct_mulVec]
  have hT : (anchoredTransport d ℓ)ᵀ = anchoredTransport d ℓ := Matrix.diagonal_transpose _
  rw [← hT, Matrix.vecMul_transpose, dyadicAnchoredFeature_transport]

def anchoredIncrement :
    ℕ → AnchoredIndex d ℓ → ℝ
  | 0 => a 0
  | j + 1 => a (j + 1) - anchoredTransport d ℓ *ᵥ a j

/-- Exact feature transport makes the actual increment field telescope. -/
theorem anchored_increment_telescope
    (x z : Covariate d) (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), dyadicAnchoredFeature j x z ⬝ᵥ anchoredIncrement a j) =
      dyadicAnchoredFeature J x z ⬝ᵥ a J := by
  induction J with
  | zero => simp [anchoredIncrement]
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    change _ +
      dyadicAnchoredFeature (J + 1) x z ⬝ᵥ
        (a (J + 1) - anchoredTransport d ℓ *ᵥ a J) = _
    rw [dotProduct_sub, dyadicAnchoredFeature_transport_dot]
    ring

end NearlyMinimax
