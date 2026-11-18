module

public import NearlyMinimax.DyadicFitBounds

@[expose] public section

/-! U2's approximation bound in the original physical cell coordinates. -/

noncomputable section
open Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

theorem dyadicCellAffine_same_cell {d : ℕ} (j : ℕ) (x y : Covariate d)
    (hcell : y ∈ dyadicPilotCell j x) :
    dyadicCellAffine j x (dyadicNormalizedAnchor j y) = y := by
  have hc : regularGridCell ((2 : ℕ) ^ j) (by positivity) y =
      regularGridCell ((2 : ℕ) ^ j) (by positivity) x := hcell
  simpa only [dyadicCellAffine, hc] using dyadicCellAffine_anchor j y

theorem dyadicPopulationFit_physical_evaluation {d ℓ : ℕ} (j : ℕ)
    (x y : Covariate d) (hcell : y ∈ dyadicPilotCell j x) (c : AnchoredIndex d ℓ → ℝ) :
    anchoredFitPolynomial (dyadicNormalizedAnchor j x) c (dyadicNormalizedAnchor j y) =
      dyadicAnchoredFeature j x y ⬝ᵥ c := by
  have he := dyadicCellAffine_same_cell j x y hcell
  unfold anchoredFitPolynomial dotProduct
  apply Finset.sum_congr rfl
  intro γ _
  have h := dyadicAnchoredFeature_affine j x (dyadicNormalizedAnchor j y) γ
  change dyadicAnchoredFeature j x (dyadicCellAffine j x (dyadicNormalizedAnchor j y)) γ = _ at h
  rw [he] at h
  change dyadicAnchoredFeature j x y γ =
    anchoredFeature (dyadicNormalizedAnchor j x) (dyadicNormalizedAnchor j y) γ at h
  rw [h]
  ring

theorem positive_rpow_times_distance (h s r : ℝ) (hh : 0 < h) :
    h ^ s * r = (h * r) * h ^ (s - 1) := by
  have he : s = (s - 1) + 1 := by ring
  conv_lhs => rw [he, Real.rpow_add hh, Real.rpow_one]
  ring

/-- The known preconditioner cancels in the genuine inverse population fit. -/
theorem dyadicPopulationFit_preconditioner_cancels {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    (dyadicPreconditionedGram (ℓ := ℓ) θ j x)⁻¹ *ᵥ
      ((dyadicKnownGram j x)⁻¹ *ᵥ (dyadicResponseMoment θ j x - θ.regression x • dyadicConstantMoment θ j x)) =
        dyadicPopulationFit θ j x := by
  have hB := (Matrix.isUnit_iff_isUnit_det _).mp (dyadicKnownGram_posDef (ℓ := ℓ) j x).isUnit
  letI := (dyadicKnownGram_posDef (ℓ := ℓ) j x).isUnit.invertible
  unfold dyadicPreconditionedGram dyadicPopulationFit
  rw [Matrix.mul_inv_rev, Matrix.inv_inv_of_invertible, Matrix.mulVec_mulVec,
    Matrix.mul_assoc _ (dyadicKnownGram j x) (dyadicKnownGram j x)⁻¹,
    Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]

end NearlyMinimax
