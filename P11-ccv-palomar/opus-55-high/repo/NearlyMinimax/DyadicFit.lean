module

public import NearlyMinimax.AnchoredFitError
public import NearlyMinimax.DyadicPilotPopulation
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Genuine original-law local polynomial fits and their Taylor approximation. -/

open MeasureTheory Set Matrix MvPolynomial
𝚺
𝚨

𝗇 𝔇 dyadicCellAffine j x
def dyadicRegressionDifference (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : 𝙀 :=
  fun w => θ.regression (𝔇 w) - θ.regression x

/-- The actual local fit, formed from original-law response and density means. -/
def dyadicPopulationFit (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : 𝗎 → ℝ :=
  (dyadicPopulationGram θ j x)⁻¹ *ᵥ
    𝙶₂

theorem dyadicCellAffine_continuous j (x : Covariate d) :
    Continuous 𝔇 := by
  apply continuous_pi
  intro i
  exact continuous_const.add $ continuous_const.mul $ continuous_apply i

𝗇 𝔊 𝘷
theorem dyadicCellAffine_mem_cube j x w
    (hw : w ∈ unitCube d) : 𝔇 w ∈ unitCube d := by
  apply gridClosedBox_subset_cube 𝔊  𝖠₃  $ regularGridCell _  𝖠₃  x
  change w ∈ gridAffine _ _ ⁻¹' gridClosedBox _ _
  rwa [gridAffine_preimage_box _  𝖠₃  _]

𝗇 𝔄 𝘎₂
theorem dyadicCellAffine_anchor j (x : Covariate d) :
    𝔇 𝔄 = x := by
  funext i
  simp only [dyadicCellAffine, gridAffine, dyadicNormalizedAnchor, gridNormalizedAnchor,
    Pi.add_apply, Pi.smul_apply]
  simp

theorem dyadicCellAffine_difference j (x w : Covariate d) :
    𝔇 w - x = (𝙉 ^ j)⁻¹ • (w - 𝔄) := by
  funext i
  simp only [dyadicCellAffine, gridAffine, dyadicNormalizedAnchor, gridNormalizedAnchor,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Nat.cast_pow]
  field_simp
  ring

theorem dyadicCellAffine_radius j x w
    (hx : 𝗌) (hw : w ∈ unitCube d) i :
    |𝔇 w i - x i| ≤ 𝗜⁻¹ := by
  have hu : 𝔄 ∈ unitCube d :=
    gridNormalizedAnchor_mem_cube 𝔊  𝖠₃  x hx
  have hi : |w i - 𝔄 i| ≤ 1 :=
    abs_le.mpr ⟨by linarith [(hw i).1, (hu i).2], by linarith [(hw i).2, (hu i).1]⟩
  have he := congrFun (dyadicCellAffine_difference j x w) i
  simp_all

theorem admissible_regression_continuousOn_cube C
    θ (hθ : 𝙟) :
    ContinuousOn θ.regression $ unitCube d := by
  obtain ⟨F, hF, hreg, hNorm⟩ := hθ.2.2.2.2.1
  exact (hreg.continuousOn.mono C.cube_subset).congr fun x hx => (hF x hx).symm

𝗃 𝔏 ἀ C θ hθ
𝗇 𝔅 (𝔏 admissible_regression_continuousOn_cube).comp (dyadicCellAffine_continuous j x).continuousOn $ dyadicCellAffine_mem_cube j x
𝗇 𝔉 dyadicRegressionDifference θ j x
theorem dyadicRegressionDifference_continuousOn C
    θ (hθ : 𝙟) j x :
    ContinuousOn 𝔉 $ unitCube d := (𝔅).sub continuousOn_const

𝗇 𝔈 dyadicNormalizedDensity θ j x
𝗇 𝔍 𝔈 w * anchoredFeature 𝔄 w γ
theorem dyadicPopulationFit_eq_normalized C
    θ (hθ : 𝙟) j (x : Covariate d) :
    dyadicPopulationFit (ℓ := ℓ) θ j x = anchoredPopulationFit 𝔄
      𝔈 𝔉 := by
  unfold dyadicPopulationFit anchoredPopulationFit
  rw [𝔏 dyadicPopulationGram_eq_normalized,
    𝔏 dyadicResponseMoment_eq_normalized, 𝔏 dyadicConstantMoment_eq_normalized]
  congr 1
  have hp : ∀ᵐ w ∂cubeVolume d, 0 ≤ 𝔈 w ∧
      𝔈 w ≤ C.densityUpper := (𝔏 dyadicNormalizedDensity_bounds j x).mono
    𝗴₁
  have hc :=
    𝔅
  rw [show 𝔉 =
     θ.regression ∘ 𝔇 - fun _ => θ.regression x by rfl,
    anchoredVectorMoment_sub _ _ _ _ (𝔏 dyadicNormalizedDensity_measurable j x)
      C.densityUpper hp hc continuousOn_const]
  congr 1
  ext γ
  change θ.regression x * ∫ w, 𝔍 * 1 ∂cubeVolume d =
      ∫ w, 𝔍 * θ.regression x ∂cubeVolume d
  rw [integral_mul_const]
  rw [integral_mul_const]
  ring
