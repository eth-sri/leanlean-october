module

public import NearlyMinimax.DyadicIncrementBias
public import NearlyMinimax.DyadicPilotRows
public import NearlyMinimax.PaperCorollaries
public import NearlyMinimax.InverseDerivativeFamily
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The true finite multiscale population residual in original U8. -/

𝛎
𝚺
𝚨
𝚭
𝚩

𝗇 𝔉 𝗎
theorem anchoredFinVector_dotProduct (u v : 𝔉 → ℝ) :
    anchoredFinVector u ⬝ᵥ anchoredFinVector v = u ⬝ᵥ v := (Fintype.equivFin 𝔉).symm.sum_comp
     fun γ => u γ * v γ

theorem dyadicPilotRow_dot_coefficients j
    x y (v : 𝔉 → ℝ) :
    dyadicPilotRow j x y ⬝ᵥ anchoredFinVector v = dyadicAnchoredFeature j x y ⬝ᵥ v :=
  anchoredFinVector_dotProduct ..

𝗇 𝔇 (EuclideanSpace.equiv ι ℝ).symm v
theorem finite_row_abs_dot_le_euclidean_norm [Fintype ι]
    row v :
    |row ⬝ᵥ v| ≤ (∑ i, |row i|) * ‖𝔇‖ := by
  apply 𝘡
  calc
     ∑ i, |row i * v i| ≤ ∑ i, |row i| * ‖𝔇‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ $ abs_nonneg _
      simpa [EuclideanSpace.equiv, Real.norm_eq_abs] using
        PiLp.norm_apply_le 𝔇 i
    𝘿 := by rw [Finset.sum_mul]

𝗇 𝔄 𝗜
𝗇 𝔅 𝙉 ^ j
𝗇 𝔊 𝔄⁻¹
𝗇 𝔍 𝔅⁻¹
theorem dyadic_scale_rpow_cancel j (s : ℝ) :
    𝔄 * 𝔊 ^ s = 𝔍 ^ (s - 1) := by
  simpa only [inv_mul_cancel₀ (by positivity : 𝔅 ≠ 0), one_mul, mul_comm] using positive_rpow_times_distance 𝔊 s 𝔄 𝖠₃

𝗇 𝔈 𝗣
def dyadicPopulationPolynomial (C : ModelConstants d) (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (y : ℝ) (m : ℕ) : Fin 𝔈 → ℝ :=
  incrementFinVector 𝔈 C.densityLower C.densityUpper
    𝖼₁ y m $ dyadicIncrementRawMean θ j x

𝗇 𝔎 C.smoothness - 1
𝗇 𝔏 𝗯
def dyadicPopulationBiasBudget (C : ModelConstants d) (J : ℕ) (m : 𝙦₁) : ℝ :=
   (𝙉 ^ J)⁻¹ ^ 𝔎 +
    ∑ j ∈ Finset.range 𝔏, 𝔍 ^ 𝔎 *
      ((m j + 1 : ℕ) : ℝ) ^ 𝔈 * Real.exp (-(m j : ℝ) * paperTau C)

def dyadicPopulationResidual (C : ModelConstants d) (θ : RegressionParameter d)
    (J : ℕ) (m : 𝙦₁) (x y : Covariate d) : ℝ :=
  θ.regression y - θ.regression x - ∑ j ∈ Finset.range 𝔏,
    dyadicPilotRow j x y ⬝ᵥ dyadicPopulationPolynomial C θ j x (θ.regression x) (m j)
