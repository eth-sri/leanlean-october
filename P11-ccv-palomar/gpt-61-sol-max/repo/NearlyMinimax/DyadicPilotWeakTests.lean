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

theorem dyadicPilotRow_field_measurable {d ℓ } j :
    Measurable (fun w : Covariate d × Covariate d => dyadicPilotRow (ℓ := ℓ) j w.1 w.2) := by
  apply measurable_pi_iff.mpr
  intro i
  exact ((anchoredMonomial_continuous (anchoredFinIndex i)).comp
    (continuous_pi (fun t => continuous_const.mul
      (((continuous_apply t).comp continuous_snd).sub
        ((continuous_apply t).comp continuous_fst))))).measurable

theorem regularPairDesignMeasure_same_cell_ae {d } (θ : RegressionParameter d)
    k hk :
    ∀ᵐ w ∂regularPairDesignMeasure θ k hk, regularGridCell k hk w.1 = regularGridCell k hk w.2 := by
  unfold regularPairDesignMeasure
  apply Measure.ae_smul_measure
  exact ae_restrict_mem (measurableSet_eq_fun
    ((regular_grid_cell_measurable k hk).comp measurable_fst)
    ((regular_grid_cell_measurable k hk).comp measurable_snd))

def dyadicPilotRowCap d ℓ j J  :=
  (anchoredDimension d ℓ : ℝ) * (2 : ℝ) ^ j * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ J)⁻¹

theorem dyadicPilotRowCap_nonneg d ℓ j J : 0 ≤ dyadicPilotRowCap d ℓ j J := by
  unfold dyadicPilotRowCap
  positivity

theorem dyadicPilotRow_pair_cap {d ℓ } C
    (θ : RegressionParameter d) (hθ : Admissible C θ) j J (hj : j ≤ J) :
    ∀ᵐ w ∂regularPairDesignMeasure θ (2 ^ J) (by positivity),
      (∑ i, |dyadicPilotRow (ℓ := ℓ) j w.1 w.2 i|) ≤ dyadicPilotRowCap d ℓ j J := by
  filter_upwards [regularPairDesignMeasure_cube_ae C θ hθ ((2 : ℕ) ^ J) (by positivity),
    regularPairDesignMeasure_same_cell_ae θ ((2 : ℕ) ^ J) (by positivity)] with w hw hc
  exact dyadicPilotRow_sum_abs_le_fine_cell j J hj w.1 w.2 hw.1 hw.2 hc.symm

def dyadicPilotErrorField {d } C θ
    n j y m z (w : Covariate d × Covariate d)  :=
  dyadicPolynomialPilot C n j w.1 y m (dyadicPilotRow j w.1 w.2) z -
    incrementFinScalar (anchoredDimension d C.order) C.densityLower C.densityUpper
      (anchoredFinTransport d C.order) y m (dyadicPilotRow j w.1 w.2)
        (dyadicIncrementRawMean θ j w.1)

/-- Every L² test of the actual centered pilot error is truly L² and has
mean zero under the original sample law. -/
theorem dyadicPilotErrorField_test_moment_facts {d } (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] θ (hθ : Admissible C θ)
    n j J (hj : j ≤ J) y (hy : |y| ≤ C.holderBound) m
    (hdegree : m + anchoredDimension d C.order + 1 ≤ n)
    ν
    (hν : MemLp ν 2 (regularPairDesignMeasure θ (2 ^ J) (by positivity))) :
    MemLp (fun z => ∫ w, ν w * dyadicPilotErrorField C θ n j y m z w
      ∂regularPairDesignMeasure θ (2 ^ J) (by positivity)) 2 (sampleLaw θ n) ∧
    (∫ z, ∫ w, ν w * dyadicPilotErrorField C θ n j y m z w
      ∂regularPairDesignMeasure θ (2 ^ J) (by positivity) ∂sampleLaw θ n) = 0 := by
  let := sampleLaw_isProbability C θ hθ n
  let M := regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity)
  let := regularPairDesignMeasure_isFinite C θ hθ ((2 : ℕ) ^ J) (by positivity)
  let R := m + anchoredDimension d C.order + 1
  let H (w : Covariate d × Covariate d) (r : Fin R) :=
    dyadicIncrementKernel C θ j w.1 y m (dyadicPilotRow j w.1 w.2) (r.val + 1)
  have hc : ∀ᵐ w ∂M, w.1 ∈ unitCube d :=
    (regularPairDesignMeasure_cube_ae C θ hθ ((2 : ℕ) ^ J) (by positivity)).mono (fun w hw => hw.1)
  have hrow := dyadicPilotRow_pair_cap (ℓ := C.order) C θ hθ j J hj
  have hH (r : Fin R) : Integrable (fun w => ν w • H w r) M :=
    dyadicIncrementKernel_weighted_integrable C θ hθ j y hy m (r.val + 1) _
      (dyadicPilotRow_field_measurable j) M (dyadicPilotRowCap d C.order j J)
      (dyadicPilotRowCap_nonneg _ _ _ _) hc hrow ν hν
  obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := incrementGlobalVector_sample_facts (ℓ := C.order) C θ hθ j
  have h := FieldLiftCovariance.integrated_centered_lift_moment_facts H ν hH
    (fun i (z : Fin n → Observation d) => incrementGlobalVector j (z i))
    (incrementGlobalMean θ j) hind hmeas hid hL2 hmean
  have heq : (fun z : Fin n → Observation d => ∫ w, ν w *
      LiftL2.centeredKernelExpansion 0 (H w)
        (fun i z => incrementGlobalVector j (z i) - incrementGlobalMean θ j) z ∂M) =
      (fun z => ∫ w, ν w * dyadicPilotErrorField C θ n j y m z w ∂M) := by
    funext z
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w => congrArg (fun a => ν w * a)
      (dyadicPolynomialPilot_centered_global C θ hθ n j w.1 y m (dyadicPilotRow j w.1 w.2) hdegree z)
  rwa [heq] at h

end NearlyMinimax
