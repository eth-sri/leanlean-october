module
public import RetunedShortPoweredFamily

@[expose] public section

open Real Complex Set Filter
open scoped BigOperators Topology ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

open Montgomery.RationalMoment

/-- The stronger curve uses the same detector with the balanced lower length. -/
theorem stronger_window {σ : ℝ} (hσ : 3/4 < σ) (hσ' : σ < 1) :
    RightDetector.PhysicalDetectorWindow σ (lowerExponent σ) := by
  have hd : 0 < 2*σ := by linarith
  refine ⟨hσ, hσ', ?_, ?_, ?_⟩
  · unfold lowerExponent
    exact (le_div_iff₀ hd).2 (by linarith)
  · unfold lowerExponent
    exact (div_lt_iff₀ hd).2 (by linarith)
  · unfold lowerExponent
    rw [show 3*(1/(2*σ))/4*(σ-1/2) = (3*(σ-1/2)/4)/(2*σ) by ring]
    exact (lt_div_iff₀ hd).2 (by linarith)

theorem window_detectorY (σ T : ℝ) : RightDetector.detectorY (lowerExponent σ) T = detectorY σ T := by
  simp [RightDetector.detectorY, RightDetector.smoothingExponent, detectorY, smoothingExponent_eq]

abbrev smoothPowerBound (σ δ : ℝ) := RightDetector.smoothPowerBound (lowerExponent σ) δ
abbrev smoothPoweredIndices (σ δ T : ℝ) := RightDetector.smoothPoweredIndices (lowerExponent σ) δ T
abbrev smoothPoweredFamilyCoefficient (η σ δ T : ℝ) :=
  RightDetector.smoothPoweredFamilyCoefficient η (lowerExponent σ) δ T
export RightDetector (smoothPoweredFamilyScale smoothPoweredFamilyScale_pos)

private theorem stronger_window_upper {σ : ℝ} (hσ : 3/4 < σ) : lowerExponent σ < 2/3 :=
  (div_lt_iff₀ (by linarith : 0 < 2*σ)).2 (by linarith)


theorem smoothPoweredIndices_card_eventually {σ : ℝ} (hσ : 3/4 < σ) (δ : ℝ) :
    ∀ᶠ T : ℝ in atTop,
      ((smoothPoweredIndices σ δ T).card : ℝ) ≤
        144*(smoothPowerBound σ δ : ℝ)^2*(Real.log T)^2 := by
  exact RightDetector.smoothPoweredIndices_card_eventually
    (one_div_pos.mpr (by linarith : 0 < 2*σ)) (stronger_window_upper hσ) δ

theorem smoothPoweredFamily_admissible {σ η : ℝ}
    (hσ : 3/4 < σ) (hη : 0 < η) (δ : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ q ∈ smoothPoweredIndices σ δ T,
      T^(lowerExponent σ) ≤ (smoothPoweredFamilyScale q : ℝ) ∧
      (smoothPoweredFamilyScale q : ℝ) ≤ (2 : ℝ)^(smoothPowerBound σ δ)*T^(smoothingExponent σ) ∧
      (smoothPoweredFamilyScale q : ℝ) ≤ T ∧
      ∀ n : ℕ, ‖smoothPoweredFamilyCoefficient η σ δ T q n‖ ≤ 1 := by
  simpa only [RightDetector.smoothingExponent, ← smoothingExponent_eq] using
    RightDetector.smoothPoweredFamily_admissible (stronger_window_upper hσ) hη δ

end MathCollab.Density.Stronger
