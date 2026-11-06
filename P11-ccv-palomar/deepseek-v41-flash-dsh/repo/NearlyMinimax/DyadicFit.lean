module

public import NearlyMinimax.AnchoredFitError
public import NearlyMinimax.DyadicPilotPopulation

@[expose] public section

/-! Genuine original-law local polynomial fits and their Taylor approximation. -/

noncomputable section
open MeasureTheory Set Matrix MvPolynomial
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

variable {d : ℕ} (j : ℕ) (x w : Covariate d)

def dyadicRegressionDifference (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : Covariate d → ℝ :=
  fun w => θ.regression (dyadicCellAffine j x w) - θ.regression x

/-- The actual local fit, formed from original-law response and density means. -/
def dyadicPopulationFit {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : AnchoredIndex d ℓ → ℝ :=
  (dyadicPopulationGram θ j x)⁻¹ *ᵥ
    (dyadicResponseMoment θ j x - θ.regression x • dyadicConstantMoment θ j x)

theorem dyadicCellAffine_continuous (x : Covariate d) :
    Continuous (dyadicCellAffine j x) := by
  apply continuous_pi
  intro i
  exact continuous_const.add (continuous_const.mul (continuous_apply i))

theorem dyadicCellAffine_mem_cube 
    (hw : w ∈ unitCube d) : dyadicCellAffine j x w ∈ unitCube d := by
  apply gridClosedBox_subset_cube ((2 : ℕ) ^ j) (by positivity) (regularGridCell _ (by positivity) x)
  change w ∈ gridAffine _ _ ⁻¹' gridClosedBox _ _
  rwa [gridAffine_preimage_box _ (by positivity) _]

theorem dyadicCellAffine_anchor (x : Covariate d) :
    dyadicCellAffine j x (dyadicNormalizedAnchor j x) = x := by
  funext i
  simp only [dyadicCellAffine, gridAffine, dyadicNormalizedAnchor, gridNormalizedAnchor,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hk : (((2 : ℕ) ^ j : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem dyadicCellAffine_difference (x w : Covariate d) :
    dyadicCellAffine j x w - x = ((2 : ℝ) ^ j)⁻¹ • (w - dyadicNormalizedAnchor j x) := by
  funext i
  simp only [dyadicCellAffine, gridAffine, dyadicNormalizedAnchor, gridNormalizedAnchor,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Nat.cast_pow, Nat.cast_ofNat]
  have hk : (2 : ℝ) ^ j ≠ 0 := by positivity
  field_simp
  ring

theorem dyadicCellAffine_radius 
    (hx : x ∈ unitCube d) (hw : w ∈ unitCube d) (i : Fin d) :
    |dyadicCellAffine j x w i - x i| ≤ ((2 : ℝ) ^ j)⁻¹ := by
  have hu : dyadicNormalizedAnchor j x ∈ unitCube d :=
    gridNormalizedAnchor_mem_cube ((2 : ℕ) ^ j) (by positivity) x hx
  have hi : |w i - dyadicNormalizedAnchor j x i| ≤ 1 :=
    abs_le.mpr ⟨by linarith [(hw i).1, (hu i).2], by linarith [(hw i).2, (hu i).1]⟩
  have he := congrFun (dyadicCellAffine_difference j x w) i
  change dyadicCellAffine j x w i - x i = ((2 : ℝ) ^ j)⁻¹ *
    (w i - dyadicNormalizedAnchor j x i) at he
  rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((2 : ℝ) ^ j)⁻¹)]
  exact (mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq (mul_one _)

section
variable (C : ModelConstants d) (θ : RegressionParameter d)

theorem admissible_regression_continuousOn_cube 
    (hθ : Admissible C θ) :
    ContinuousOn θ.regression (unitCube d) := by
  obtain ⟨F, hF, hreg, hNorm⟩ := hθ.2.2.2.2.1
  exact (hreg.continuousOn.mono C.cube_subset).congr (fun x hx => (hF x hx).symm)

theorem dyadicRegressionDifference_continuousOn 
    (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    ContinuousOn (dyadicRegressionDifference θ j x) (unitCube d) := ((admissible_regression_continuousOn_cube C θ hθ).comp
    (dyadicCellAffine_continuous j x).continuousOn (dyadicCellAffine_mem_cube j x)).sub continuousOn_const

end

theorem dyadicPopulationFit_eq_normalized {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    dyadicPopulationFit (ℓ := ℓ) θ j x = anchoredPopulationFit (dyadicNormalizedAnchor j x)
      (dyadicNormalizedDensity θ j x) (dyadicRegressionDifference θ j x) := by
  unfold dyadicPopulationFit anchoredPopulationFit
  rw [dyadicPopulationGram_eq_normalized C θ hθ,
    dyadicResponseMoment_eq_normalized C θ hθ, dyadicConstantMoment_eq_normalized C θ hθ]
  congr 1
  have hp : ∀ᵐ w ∂cubeVolume d, 0 ≤ dyadicNormalizedDensity θ j x w ∧
      dyadicNormalizedDensity θ j x w ≤ C.densityUpper := (dyadicNormalizedDensity_bounds C θ hθ j x).mono
    (fun w hw => ⟨C.densityLower_pos.le.trans hw.1, hw.2⟩)
  have hc : ContinuousOn (θ.regression ∘ dyadicCellAffine j x) (unitCube d) :=
    (admissible_regression_continuousOn_cube C θ hθ).comp
      (dyadicCellAffine_continuous j x).continuousOn (dyadicCellAffine_mem_cube j x)
  rw [show dyadicRegressionDifference θ j x =
    (θ.regression ∘ dyadicCellAffine j x) - (fun _ => θ.regression x) by rfl,
    anchoredVectorMoment_sub _ _ _ _ (dyadicNormalizedDensity_measurable C θ hθ j x)
      C.densityUpper hp hc continuousOn_const]
  congr 1
  ext γ
  change θ.regression x * (∫ w, dyadicNormalizedDensity θ j x w *
    anchoredFeature (dyadicNormalizedAnchor j x) w γ * 1 ∂cubeVolume d) =
      ∫ w, dyadicNormalizedDensity θ j x w *
        anchoredFeature (dyadicNormalizedAnchor j x) w γ * θ.regression x ∂cubeVolume d
  rw [integral_mul_const]
  simp only [mul_one]
  rw [integral_mul_const]
  ring

end NearlyMinimax
