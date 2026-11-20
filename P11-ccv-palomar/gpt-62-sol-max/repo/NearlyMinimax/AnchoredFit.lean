module

public import NearlyMinimax.DyadicGram
public import NearlyMinimax.AnchoredBasis

@[expose] public section

/-! Actual population normal equations, polynomial reproduction and telescoping. -/

noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

def anchoredPopulationFit {d ℓ : ℕ} (u : Covariate d) (p g : Covariate d → ℝ) :
    AnchoredIndex d ℓ → ℝ := (anchoredDensityGram u p)⁻¹ *ᵥ anchoredVectorMoment u p g

section
variable {d ℓ : ℕ}

section
variable (u : Covariate d)

theorem anchoredPopulationFit_normal_equation
    (p g : Covariate d → ℝ) (hpmeas : Measurable p) (a b : ℝ) (ha : 0 < a)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) :
    anchoredDensityGram (ℓ := ℓ) u p *ᵥ anchoredPopulationFit u p g =
      anchoredVectorMoment u p g := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp
    (anchoredDensityGram_posDef (ℓ := ℓ) u p hpmeas a b ha hp).isUnit
  rw [anchoredPopulationFit, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

theorem anchoredVectorMoment_polynomial
    (p : Covariate d → ℝ) (hpmeas : Measurable p) (b : ℝ)
    (hp : ∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b) (c : AnchoredIndex d ℓ → ℝ) :
    anchoredVectorMoment u p (anchoredFitPolynomial u c) = anchoredDensityGram u p *ᵥ c := by
  ext γ
  exact (weighted_gram_mulVec (cubeVolume d) p (anchoredFeature u) c
    (anchoredDensityGram_product_integrable u p hpmeas b hp) γ).2

end

theorem dyadicAnchoredFeature_transport_dot (j : ℕ) (x z : Covariate d)
    (c : AnchoredIndex d ℓ → ℝ) :
    dyadicAnchoredFeature (j + 1) x z ⬝ᵥ (anchoredTransport d ℓ *ᵥ c) =
      dyadicAnchoredFeature j x z ⬝ᵥ c := by
  rw [Matrix.dotProduct_mulVec]
  have hT : (anchoredTransport d ℓ)ᵀ = anchoredTransport d ℓ := Matrix.diagonal_transpose _
  rw [← hT, Matrix.vecMul_transpose, dyadicAnchoredFeature_transport]

end

def anchoredIncrement {d ℓ : ℕ} (a : ℕ → AnchoredIndex d ℓ → ℝ) :
    ℕ → AnchoredIndex d ℓ → ℝ
  | 0 => a 0
  | j + 1 => a (j + 1) - anchoredTransport d ℓ *ᵥ a j

/-- Exact feature transport makes the actual increment field telescope. -/
theorem anchored_increment_telescope {d ℓ : ℕ} (a : ℕ → AnchoredIndex d ℓ → ℝ)
    (x z : Covariate d) (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), dyadicAnchoredFeature j x z ⬝ᵥ anchoredIncrement a j) =
      dyadicAnchoredFeature J x z ⬝ᵥ a J := by
  induction J with
  | zero => simp [anchoredIncrement]
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    change dyadicAnchoredFeature J x z ⬝ᵥ a J +
      dyadicAnchoredFeature (J + 1) x z ⬝ᵥ
        (a (J + 1) - anchoredTransport d ℓ *ᵥ a J) = _
    rw [dotProduct_sub, dyadicAnchoredFeature_transport_dot]
    ring

end NearlyMinimax
