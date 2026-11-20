module

public import NearlyMinimax.AnchoredMoments
public import NearlyMinimax.PopulationInverseDerivatives


@[expose] public section

/-! The inverse derivative chart evaluated at genuine bounded population moments. -/

noncomputable section
namespace NearlyMinimax
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

variable {d ℓ : ℕ}

/-- The two population vector families are the density-feature moment and the
response-feature moment, with the known Lebesgue Gram preconditioner. -/
def anchoredFinMomentFamilies (u : Covariate d)
    (p f : Covariate d → ℝ) : Bool → Fin (anchoredDimension d ℓ) → ℝ :=
  fun t i => anchoredPreconditionedMoment u p (if t then fun _ => 1 else f)
    ((Fintype.equivFin (AnchoredIndex d ℓ)).symm i)

theorem anchoredFinMomentFamilies_uniform_bound
    {b F : ℝ} (hb : 0 ≤ b) (hF : 0 ≤ F) :
    ∃ W : ℝ, 0 < W ∧ ∀ u ∈ unitCube d, ∀ p f,
      (∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b) →
      (∀ w ∈ unitCube d, |f w| ≤ F) →
      ∀ t, ‖anchoredFinMomentFamilies (ℓ := ℓ) u p f t‖ ≤ W := by
  obtain ⟨W, hW, hm⟩ := anchoredPreconditionedMoment_uniform_bound (ℓ := ℓ) b (max 1 F) hb (by positivity)
  refine ⟨W, hW, ?_⟩
  intro u hu p f hp hf t
  apply (pi_norm_le_iff_of_nonneg hW.le).mpr
  intro i
  exact (norm_le_pi_norm _ ((Fintype.equivFin (AnchoredIndex d ℓ)).symm i)).trans (hm u hu p _ hp (by
    intro w hw
    bound))

end NearlyMinimax
