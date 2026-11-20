module

public import NearlyMinimax.AnchoredFitError
public import NearlyMinimax.DyadicPilotPopulation

@[expose] public section

/-! Genuine original-law local polynomial fits and their Taylor approximation. -/

noncomputable section
open MeasureTheory Set Matrix MvPolynomial
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

def dyadicRegressionDifference {d : ℕ} (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : Covariate d → ℝ :=
  fun w => θ.regression (dyadicCellAffine j x w) - θ.regression x

/-- The actual local fit, formed from original-law response and density means. -/
def dyadicPopulationFit {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : AnchoredIndex d ℓ → ℝ :=
  (dyadicPopulationGram θ j x)⁻¹ *ᵥ
    (dyadicResponseMoment θ j x - θ.regression x • dyadicConstantMoment θ j x)

section
variable {d : ℕ}

section
variable (j : ℕ)

theorem dyadicCellAffine_continuous (x : Covariate d) :
    Continuous (dyadicCellAffine j x) := by
  apply continuous_const.add <;> fun_prop

theorem dyadicCellAffine_mem_cube (x w : Covariate d)
    (hw : w ∈ unitCube d) : dyadicCellAffine j x w ∈ unitCube d := by
  apply gridClosedBox_subset_cube ((2 : ℕ) ^ j) (by positivity) (regularGridCell _ (by positivity) x)
  change w ∈ gridAffine _ _ ⁻¹' gridClosedBox _ _
  rwa [gridAffine_preimage_box _ (by positivity) _]

theorem dyadicCellAffine_anchor (x : Covariate d) :
    dyadicCellAffine j x (dyadicNormalizedAnchor j x) = x := by
  funext i
  simp only [dyadicCellAffine, gridAffine, dyadicNormalizedAnchor, gridNormalizedAnchor,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp

section
variable (x w : Covariate d)

theorem dyadicCellAffine_difference :
    dyadicCellAffine j x w - x = ((2 : ℝ) ^ j)⁻¹ • (w - dyadicNormalizedAnchor j x) := by
  funext i
  simp only [dyadicCellAffine, gridAffine, dyadicNormalizedAnchor, gridNormalizedAnchor,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Nat.cast_pow, Nat.cast_ofNat]
  field_simp <;> ring

theorem dyadicCellAffine_radius
    (hx : x ∈ unitCube d) (hw : w ∈ unitCube d) (i : Fin d) :
    |dyadicCellAffine j x w i - x i| ≤ ((2 : ℝ) ^ j)⁻¹ := by
  have hu : dyadicNormalizedAnchor j x ∈ unitCube d :=
    gridNormalizedAnchor_mem_cube ((2 : ℕ) ^ j) (by positivity) x hx
  have hi := unitCube_coord_sub_abs_le_one hw hu i
  have he := congrFun (dyadicCellAffine_difference j x w) i
  change dyadicCellAffine j x w i - x i = ((2 : ℝ) ^ j)⁻¹ *
    (w i - dyadicNormalizedAnchor j x i) at he
  simp_all [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((2 : ℝ) ^ j)⁻¹)]

end

end

section
variable (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
include hθ

theorem admissible_regression_continuousOn_cube :
    ContinuousOn θ.regression (unitCube d) := by
  obtain ⟨F, hF, hreg, hNorm⟩ := hθ.2.2.2.2.1
  exact (hreg.continuousOn.mono C.cube_subset).congr (fun x hx => (hF x hx).symm)

theorem dyadicRegressionDifference_continuousOn (j : ℕ) (x : Covariate d) :
    ContinuousOn (dyadicRegressionDifference θ j x) (unitCube d) := by
  exact ((admissible_regression_continuousOn_cube C θ hθ).comp
    (dyadicCellAffine_continuous j x).continuousOn (dyadicCellAffine_mem_cube j x)).sub continuousOn_const

end

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
  have hc :=
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
  simp [integral_mul_const] <;> linarith

end NearlyMinimax
