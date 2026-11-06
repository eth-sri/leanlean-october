module

public import NearlyMinimax.IncrementKernelMeasurability
public import NearlyMinimax.DyadicPilotRows
public import NearlyMinimax.BoundedPairMeanOperators
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual universal-test covariance for the dyadic polynomial pilot under
the paper's original weighted same-cell pair measure. -/
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
𝚨
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 300000
𝚩

𝗇 𝔈 𝙩
𝗇 𝔉 dyadicPilotRow (ℓ := ℓ) j w.1 w.2
theorem dyadicPilotRow_field_measurable j :
    Measurable fun w : 𝔈 => 𝔉 := by
  apply measurable_pi_iff.mpr
  intro i
  exact ((anchoredMonomial_continuous $ anchoredFinIndex i ).comp
    $ continuous_pi fun t => continuous_const.mul
      $ ((continuous_apply t).comp continuous_snd).sub
        $ (continuous_apply t).comp continuous_fst ).measurable

𝗃 𝔒 (regular_grid_cell_measurable k hk).comp ἀ
theorem regularPairDesignMeasure_same_cell_ae (θ : RegressionParameter d)
    k hk :
    ∀ᵐ w ∂𝗪₁, 𝘯 w.1 = 𝘯 w.2 := by
  apply Measure.ae_smul_measure
  exact ae_restrict_mem $ measurableSet_eq_fun
    𝔒 measurable_fst
    𝔒 measurable_snd

def dyadicPilotRowCap (d ℓ j J : ℕ) : ℝ :=
  (𝚃 : ℝ) * 𝙉 ^ j * Real.sqrt 𝙊 * (𝙉 ^ J)⁻¹

𝗃 𝔓 dyadicPilotRowCap d ἀ j J
theorem dyadicPilotRowCap_nonneg d ℓ j J : 0 ≤ 𝔓 ℓ := by
  unfold dyadicPilotRowCap
  positivity

𝗇 𝔄 𝗟 ^ J
𝗇 𝔊 regularPairDesignMeasure θ 𝔄
𝗇 𝔎 2 ^ J
𝗃 𝔑 ἀ C θ hθ
theorem dyadicPilotRow_pair_cap C
    (θ : RegressionParameter d) (hθ : 𝙟) (j J : ℕ) (hj : j ≤ J) :
    ∀ᵐ w ∂𝔊 𝖠₃ ,
       ∑ i, |𝔉 i| ≤ 𝔓 ℓ := by
  filter_upwards [𝔑 regularPairDesignMeasure_cube_ae 𝔎 𝖠₃ ,
    regularPairDesignMeasure_same_cell_ae θ 𝔎 𝖠₃ ] with w hw hc
  exact dyadicPilotRow_sum_abs_le_fine_cell j J hj w.1 w.2 hw.1 hw.2 hc.symm

𝗇 𝔇 dyadicPilotRow j w.1 w.2
𝗇 𝔍 𝙌
𝗇 𝔏 𝗣
def dyadicPilotErrorField (C : ModelConstants d) (θ : RegressionParameter d)
    (n j : ℕ) (y : ℝ) (m : ℕ) (z : 𝔍) (w : 𝔈) : ℝ :=
  dyadicPolynomialPilot C n j w.1 y m 𝔇 z -
    incrementFinScalar 𝔏 C.densityLower C.densityUpper
      𝖼₁ y m 𝔇
        (dyadicIncrementRawMean θ j w.1)

𝗇 𝔅 ν w * dyadicPilotErrorField C θ n j y m z w
𝗇 𝔐 𝗙₁
𝗃 𝔔 ἀ (ℓ := C.order) C θ hθ j
/-- Every L² test of the actual centered pilot error is truly L² and has
mean zero under the original sample law. -/
theorem dyadicPilotErrorField_test_moment_facts (C : ModelConstants d)
    [Nonempty 𝘘] (θ : RegressionParameter d) (hθ : 𝙟)
    (n j J : ℕ) (hj : j ≤ J) (y : ℝ) (hy : |y| ≤ C.holderBound) (m : ℕ)
    (hdegree : m + 𝔏 + 1 ≤ n)
    (ν : 𝔈 → ℝ)
    (hν : MemLp ν 2 $ 𝔊 𝖠₃ ) :
    MemLp (fun z => ∫ w, 𝔅
      ∂𝔊  𝖠₃ ) 2 (sampleLaw θ n) ∧
     ∫ z, ∫ w, 𝔅
      ∂𝔊  𝖠₃  ∂sampleLaw θ n = 0 := by
  let := 𝔑 sampleLaw_isProbability n
  let M := 𝔊 𝖠₃
  let := 𝔑 regularPairDesignMeasure_isFinite 𝔄 𝖠₃
  let R := m + 𝔏 + 1
  let H (w : 𝔈) (r : Fin R) :=
    𝖳₂ w.1 y m 𝔇 𝔐
  have hc : 𝖶₂ :=
    (𝔑 regularPairDesignMeasure_cube_ae 𝔄 𝖠₃ ).mono fun w hw => hw.1
  have hrow := 𝔔 dyadicPilotRow_pair_cap J hj
  have hH (r : Fin R) : Integrable (fun w => ν w • H w r) M :=
    𝔑 dyadicIncrementKernel_weighted_integrable j y hy m 𝔐 _
      (dyadicPilotRow_field_measurable j) M 𝔓 C.order
      (dyadicPilotRowCap_nonneg _ _ _ _) hc hrow ν hν
  obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := 𝔔 incrementGlobalVector_sample_facts
  have h := FieldLiftCovariance.integrated_centered_lift_moment_facts H ν hH
    (fun i (z : 𝔍) => 𝗤₁)
    𝚆₁ hind hmeas hid hL2 hmean
  have heq : (fun z : 𝔍 => ∫ w, ν w *
      LiftL2.centeredKernelExpansion 0 (H w)
        (fun i z => 𝗤₁ - 𝚆₁) z ∂M) =
       fun z => ∫ w, 𝔅 ∂M := by
    funext z
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w => congrArg (fun a => ν w * a)
      $ 𝔑 dyadicPolynomialPilot_centered_global n j w.1 y m 𝔇 hdegree z
  aesop
