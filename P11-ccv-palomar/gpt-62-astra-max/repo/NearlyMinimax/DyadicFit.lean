module

public import NearlyMinimax.AnchoredFitError
public import NearlyMinimax.DyadicPilotPopulation

@[expose] public section

/-! Genuine original-law local polynomial fits and their Taylor approximation. -/

noncomputable section
open MeasureTheory Set Matrix MvPolynomial
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

section
variable {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ) (x : Covariate d)

def dyadicRegressionDifference : Covariate d → ℝ :=
  fun w => θ.regression (dyadicCellAffine j x w) - θ.regression x

/-- The actual local fit, formed from original-law response and density means. -/
def dyadicPopulationFit : AnchoredIndex d ℓ → ℝ :=
  (dyadicPopulationGram θ j x)⁻¹ *ᵥ
    (dyadicResponseMoment θ j x - θ.regression x • dyadicConstantMoment θ j x)

theorem dyadicCellAffine_continuous :
    Continuous (dyadicCellAffine j x) := by
  apply continuous_pi
  intro i
  exact continuous_const.add (continuous_const.mul (continuous_apply i))

theorem dyadicCellAffine_mem_cube (w : Covariate d)
    (hw : w ∈ unitCube d) : dyadicCellAffine j x w ∈ unitCube d := by
  apply gridClosedBox_subset_cube (k := (2 ^ j)) (by positivity) (regularGridCell _ (by positivity) x)
  change w ∈ gridAffine _ ⁻¹' gridClosedBox _
  rwa [gridAffine_preimage_box _ (by positivity) _]

theorem dyadicCellAffine_anchor :
    dyadicCellAffine j x (dyadicNormalizedAnchor j x) = x := by
  ext <;> simp [dyadicCellAffine, gridAffine, dyadicNormalizedAnchor, gridNormalizedAnchor]

theorem dyadicCellAffine_difference (w : Covariate d) :
    dyadicCellAffine j x w - x = ((2 : ℝ) ^ j)⁻¹ • (w - dyadicNormalizedAnchor j x) := by
  funext i
  simp [dyadicCellAffine, gridAffine, dyadicNormalizedAnchor, gridNormalizedAnchor]
  field_simp
  ring

theorem dyadicCellAffine_radius {x w : Covariate d}
    (hx : x ∈ unitCube d) (hw : w ∈ unitCube d) (i : Fin d) :
    |dyadicCellAffine j x w i - x i| ≤ (2 ^ j)⁻¹ := by
  have hu : dyadicNormalizedAnchor j x ∈ unitCube d :=
    gridNormalizedAnchor_mem_cube _ (by positivity) hx
  have hi : |w i - dyadicNormalizedAnchor j x i| ≤ 1 :=
    abs_le.mpr ⟨by linarith [(hw i).1, (hu i).2], by linarith [(hw i).2, (hu i).1]⟩
  have he := congrFun (dyadicCellAffine_difference j x w) i
  simp_all

end

variable {d ℓ : ℕ} {C : ModelConstants d} {θ : RegressionParameter d} (hθ : Admissible C θ) (j : ℕ)
include hθ

theorem admissible_regression_continuousOn_cube :
    ContinuousOn θ.regression (unitCube d) := by
  obtain ⟨F, hF, hreg, hNorm⟩ := hθ.2.2.2.2.1
  exact (hreg.continuousOn.mono C.cube_subset).congr (fun x hx => (hF x hx).symm)

theorem dyadicRegressionDifference_continuousOn (x : Covariate d) :
    ContinuousOn (dyadicRegressionDifference θ j x) (unitCube d) := ((admissible_regression_continuousOn_cube hθ).comp
    (dyadicCellAffine_continuous j x).continuousOn (dyadicCellAffine_mem_cube j x)).sub continuousOn_const

theorem dyadicPopulationFit_eq_normalized (x : Covariate d) :
    dyadicPopulationFit (ℓ := ℓ) θ j x = anchoredPopulationFit (dyadicNormalizedAnchor j x)
      (dyadicNormalizedDensity θ j x) (dyadicRegressionDifference θ j x) := by
  unfold dyadicPopulationFit anchoredPopulationFit
  rw [dyadicPopulationGram_eq_normalized hθ,
    dyadicResponseMoment_eq_normalized hθ, dyadicConstantMoment_eq_normalized hθ]
  congr 1
  have hc  :=
    (admissible_regression_continuousOn_cube hθ).comp
      (dyadicCellAffine_continuous j x).continuousOn (dyadicCellAffine_mem_cube j x)
  rw [show dyadicRegressionDifference θ j x =
    (θ.regression ∘ dyadicCellAffine j x) - (fun _ => θ.regression x) by rfl,
    anchoredVectorMoment_sub _ _ _ _ (dyadicNormalizedDensity_measurable hθ j x) ((dyadicNormalizedDensity_bounds hθ j x).mono (fun w hw => ⟨C.densityLower_pos.le.trans hw.1, hw.2⟩)) hc continuousOn_const]
  congr 1
  ext γ
  change θ.regression x * (∫ w, dyadicNormalizedDensity θ j x w *
    anchoredFeature (dyadicNormalizedAnchor j x) w γ * 1 ∂cubeVolume d) =
      ∫ w, dyadicNormalizedDensity θ j x w *
        anchoredFeature (dyadicNormalizedAnchor j x) w γ * θ.regression x ∂cubeVolume d
  simp
  rw [integral_mul_const]
  ring

end NearlyMinimax
