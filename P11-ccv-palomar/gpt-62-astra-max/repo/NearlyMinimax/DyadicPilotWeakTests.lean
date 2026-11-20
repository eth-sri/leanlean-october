module

public import NearlyMinimax.IncrementKernelMeasurability
public import NearlyMinimax.DyadicPilotRows
public import NearlyMinimax.BoundedPairMeanOperators

@[expose] public section

/-! Actual universal-test covariance for the dyadic polynomial pilot under
the paper's original weighted same-cell pair measure. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)

theorem dyadicPilotRow_field_measurable {ℓ : ℕ} (j : ℕ) :
    Measurable (fun w : Covariate d × Covariate d => dyadicPilotRow (ℓ := ℓ) j w.1 w.2) := by
  apply measurable_pi_iff.mpr
  intro i
  exact ((anchoredMonomial_continuous (anchoredFinIndex i)).comp
    (by fun_prop)).measurable

def dyadicPilotRowCap (d ℓ j J : ℕ) : ℝ :=
  (anchoredDimension d ℓ) * 2 ^ j * Real.sqrt d * (2 ^ J)⁻¹

theorem dyadicPilotRowCap_nonneg (d ℓ j J : ℕ) : 0 ≤ dyadicPilotRowCap d ℓ j J := by
  unfold dyadicPilotRowCap
  positivity

theorem dyadicPilotRow_pair_cap {ℓ : ℕ} {C : ModelConstants d}
    {θ : RegressionParameter d} (hθ : Admissible C θ) {j J : ℕ} (hj : j ≤ J) :
    ∀ᵐ w ∂dyadicPairDesignMeasure θ J,
      (∑ i, |dyadicPilotRow (ℓ := ℓ) j w.1 w.2 i|) ≤ dyadicPilotRowCap d ℓ j J := by
  filter_upwards [regularPairDesignMeasure_cube_ae hθ (2 ^ J) (by positivity),
    (by apply Measure.ae_smul_measure; exact ae_restrict_mem (measurableSet_eq_fun ((regular_grid_cell_measurable (2 ^ J) (by positivity)).comp measurable_fst) ((regular_grid_cell_measurable (2 ^ J) (by positivity)).comp measurable_snd)))] with w hw hc
  exact dyadicPilotRow_sum_abs_le_fine_cell hj hw.1 hw.2 hc.symm

def dyadicPilotErrorField
    {n : ℕ} (j : ℕ) (y : ℝ) (m : ℕ) (z : Fin n → Observation d) (w : Covariate d × Covariate d) : ℝ :=
  dyadicPolynomialPilot (C := C) n j w.1 y m (dyadicPilotRow j w.1 w.2) z -
    incrementFinScalar C.densityLower C.densityUpper
      (anchoredFinTransport d C.order) y m (dyadicPilotRow j w.1 w.2)
        (dyadicIncrementRawMean θ j w.1)

/-- Every L² test of the actual centered pilot error is truly L² and has
mean zero under the original sample law. -/
theorem dyadicPilotErrorField_test_moment_facts {C : ModelConstants d}
    [Nonempty (AnchoredIndex d C.order)] {θ : RegressionParameter d} (hθ : Admissible C θ)
    {n j J : ℕ} (hj : j ≤ J) {y : ℝ} (hy : |y| ≤ C.holderBound) {m : ℕ}
    (hdegree : m + anchoredDimension d C.order + 1 ≤ n)
    {ν : Covariate d × Covariate d → ℝ}
    (hν : MemLp ν 2 (dyadicPairDesignMeasure θ J)) :
    MemLp (fun z => ∫ w, ν w * dyadicPilotErrorField C θ j y m z w
      ∂dyadicPairDesignMeasure θ J) 2 (sampleLaw θ n) ∧
    (∫ z, ∫ w, ν w * dyadicPilotErrorField C θ j y m z w
      ∂dyadicPairDesignMeasure θ J ∂sampleLaw θ n) = 0 := by
  let := sampleLaw_isProbability C θ hθ n
  let M := dyadicPairDesignMeasure θ J
  let := regularPairDesignMeasure_isFinite hθ (2 ^ J) (by positivity)
  let R := m + anchoredDimension d C.order + 1
  let H (w : Covariate d × Covariate d) (r : Fin R) :=
    dyadicIncrementKernel (C := C) θ j w.1 y m (dyadicPilotRow j w.1 w.2) (r.val + 1)
  have hc  :=
    (regularPairDesignMeasure_cube_ae hθ (2 ^ J) (by positivity)).mono (fun w hw => hw.1)
  have hrow := dyadicPilotRow_pair_cap (ℓ := C.order) hθ hj
  have hH (r : Fin R)  :=
    dyadicIncrementKernel_weighted_integrable hθ j hy m (r.val + 1)
      (dyadicPilotRow_field_measurable j)
      (dyadicPilotRowCap_nonneg ..) hc hrow hν
  obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := incrementGlobalVector_sample_facts hθ j
  have h := FieldLiftCovariance.integrated_centered_lift_moment_facts hH
    (X := (fun i (z : Fin n → Observation d) => incrementGlobalVector j (z i))) hind hmeas hid hL2 hmean
  have heq : (fun z : Fin n → Observation d => ∫ w, ν w *
      LiftL2.centeredKernelExpansion 0 (H w)
        (fun i z => incrementGlobalVector j (z i) - incrementGlobalMean θ j) z ∂M) =
      (fun z => ∫ w, ν w * dyadicPilotErrorField C θ j y m z w ∂M) := by
    funext z
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w => congrArg (fun a => ν w * a)
      (dyadicPolynomialPilot_centered_global hθ n j w.1 y (dyadicPilotRow j w.1 w.2) hdegree z)
  rwa [heq] at h

end NearlyMinimax
