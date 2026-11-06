module

public import NearlyMinimax.DyadicFitBounds
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! U2's approximation bound in the original physical cell coordinates. -/

open Set Matrix
𝚺
𝚨

𝗇 𝔄 dyadicNormalizedAnchor j y
𝗇 𝔇 𝘷
𝗃 𝔊 ἀ j x
theorem dyadicCellAffine_same_cell j (x y : Covariate d)
    (hcell : y ∈ 𝔊 dyadicPilotCell) :
    𝔊 dyadicCellAffine 𝔄 = y := by
  have hc : regularGridCell 𝔇  𝖠₃  y =
      regularGridCell 𝔇  𝖠₃  x := hcell
  simpa only [dyadicCellAffine, hc] using dyadicCellAffine_anchor j y

𝗇 𝔈 𝔊 dyadicNormalizedAnchor
theorem dyadicPopulationFit_physical_evaluation j
    x y (hcell : y ∈ 𝔊 dyadicPilotCell) (c : 𝗎 → ℝ) :
    anchoredFitPolynomial 𝔈 c 𝔄 =
      𝔊 dyadicAnchoredFeature y ⬝ᵥ c := by
  apply Finset.sum_congr rfl
  intro γ _
  have h := 𝔊 dyadicAnchoredFeature_affine 𝔄 γ
  change 𝔊 dyadicAnchoredFeature (𝔊 dyadicCellAffine 𝔄) γ = _ at h
  rw [ 𝔊 dyadicCellAffine_same_cell y hcell ] at h
  change 𝔊 dyadicAnchoredFeature y γ =
    anchoredFeature 𝔈 𝔄 γ at h
  grind

𝗇 𝔉 s - 1
theorem positive_rpow_times_distance (h s r : ℝ) (hh : 0 < h) :
    h ^ s * r = h * r * h ^ 𝔉 := by
  have he : s = 𝔉 + 1 := 𝖢₃
  conv_lhs => rw [he, Real.rpow_add hh, Real.rpow_one]
  ring

𝗇 𝔅 𝔊 dyadicKnownGram
/-- The known preconditioner cancels in the genuine inverse population fit. -/
theorem dyadicPopulationFit_preconditioner_cancels C
    θ (hθ : 𝙟) j (x : Covariate d) :
    (dyadicPreconditionedGram (ℓ := ℓ) θ j x)⁻¹ *ᵥ
       𝔅⁻¹ *ᵥ 𝙶₂ =
        dyadicPopulationFit θ j x := by
  letI := (dyadicKnownGram_posDef (ℓ := ℓ) j x).isUnit.invertible
  unfold dyadicPreconditionedGram dyadicPopulationFit
  rw [Matrix.mul_inv_rev, Matrix.inv_inv_of_invertible, Matrix.mulVec_mulVec,
    Matrix.mul_assoc _ 𝔅 𝔅⁻¹,
    Matrix.mul_nonsing_inv _ $ (Matrix.isUnit_iff_isUnit_det _).mp (𝔊 dyadicKnownGram_posDef).isUnit , Matrix.mul_one]
