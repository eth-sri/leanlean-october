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

theorem dyadicPilotRow_field_measurable {d ℓ : ℕ} (j : ℕ) :
    Measurable (fun w : CovariatePair d => dyadicPilotRow (ℓ := ℓ) j w.1 w.2) := by
  apply measurable_pi_iff.mpr
  intro i
  exact ((anchoredMonomial_continuous (anchoredFinIndex i)).comp
    (continuous_pi (fun t => continuous_const.mul
      (((continuous_apply t).comp continuous_snd).sub
        ((continuous_apply t).comp continuous_fst))))).measurable

theorem regularPairDesignMeasure_same_cell_ae {d : ℕ} (θ : RegressionParameter d)
    (k : ℕ) (hk : 0 < k) :
    ∀ᵐ w ∂regularPairDesignMeasure θ k hk, regularGridCell k hk w.1 = regularGridCell k hk w.2 := by
  unfold regularPairDesignMeasure
  apply Measure.ae_smul_measure
  exact ae_restrict_mem (measurableSet_eq_fun
    ((regular_grid_cell_measurable k hk).comp measurable_fst)
    ((regular_grid_cell_measurable k hk).comp measurable_snd))

def dyadicPilotRowCap (d ℓ j J : ℕ) : ℝ :=
  (anchoredDimension d ℓ : ℝ) * (2 : ℝ) ^ j * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ J)⁻¹

theorem dyadicPilotRowCap_nonneg (d ℓ j J : ℕ) : 0 ≤ dyadicPilotRowCap d ℓ j J := by
  unfold dyadicPilotRowCap
  positivity

theorem dyadicPilotRow_pair_cap {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j J : ℕ) (hj : j ≤ J) :
    ∀ᵐ w ∂regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity),
      (∑ i, |dyadicPilotRow (ℓ := ℓ) j w.1 w.2 i|) ≤ dyadicPilotRowCap d ℓ j J := by
  filter_upwards [regularPairDesignMeasure_cube_ae C θ hθ ((2 : ℕ) ^ J) (by positivity),
    regularPairDesignMeasure_same_cell_ae θ ((2 : ℕ) ^ J) (by positivity)] with w hw hc
  exact dyadicPilotRow_sum_abs_le_fine_cell j J hj w.1 w.2 hw.1 hw.2 hc.symm

def dyadicPilotErrorField {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (n j : ℕ) (y : ℝ) (m : ℕ) (z : ObservedSample d n) (w : CovariatePair d) : ℝ :=
  dyadicPolynomialPilot C n j w.1 y m (dyadicPilotRow j w.1 w.2) z -
    incrementFinScalar (anchoredDimension d C.order) C.densityLower C.densityUpper
      (anchoredFinTransport d C.order) y m (dyadicPilotRow j w.1 w.2)
        (dyadicIncrementRawMean θ j w.1)

section PairKernels
variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)

def dyadicPairKernel (j : ℕ) (y : ℝ) (m : ℕ) (w : CovariatePair d)
    (r : Fin (m + anchoredDimension d C.order + 1)) :=
  dyadicIncrementKernel C θ j w.1 y m (dyadicPilotRow j w.1 w.2) (r.val + 1)

variable [Nonempty (AnchoredIndex d C.order)] (hθ : Admissible C θ)
include hθ

theorem dyadicPairKernel_measurable (j : ℕ) (y : ℝ) (m : ℕ) (r : Fin (m + anchoredDimension d C.order + 1)) :
    Measurable (fun w => dyadicPairKernel C θ j y m w r) :=
  dyadicIncrementKernel_field_measurable C θ hθ j y m _ _ (dyadicPilotRow_field_measurable j)

section
variable (j J : ℕ) (hj : j ≤ J) (y : ℝ) (hy : |y| ≤ C.holderBound)
    (m : ℕ)
include hj hy

theorem dyadicPairKernel_bounded (r : Fin (m + anchoredDimension d C.order + 1)) :
    ∃ B : ℝ, 0 < B ∧ ∀ᵐ w ∂regularPairDesignMeasure θ (2 ^ J) (by positivity),
      ‖dyadicPairKernel C θ j y m w r‖ ≤ B :=
  dyadicIncrementKernel_field_norm_bound C θ hθ j y hy m _ _ _ _
    (dyadicPilotRowCap_nonneg d C.order j J)
    ((regularPairDesignMeasure_cube_ae C θ hθ (2 ^ J) (by positivity)).mono fun _ hw => hw.1)
    (dyadicPilotRow_pair_cap C θ hθ j J hj)

theorem dyadicPairKernel_weighted_integrable (ν : CovariatePair d → ℝ)
    (hν : MemLp ν 2 (regularPairDesignMeasure θ (2 ^ J) (by positivity)))
    (r : Fin (m + anchoredDimension d C.order + 1)) :
    Integrable (fun w => ν w • dyadicPairKernel C θ j y m w r)
      (regularPairDesignMeasure θ (2 ^ J) (by positivity)) := by
  let := regularPairDesignMeasure_isFinite C θ hθ (2 ^ J) (by positivity)
  obtain ⟨B, _, hB⟩ := dyadicPairKernel_bounded C θ hθ j J hj y hy m r
  exact (hν.integrable (by norm_num)).smul_bdd B
    (dyadicPairKernel_measurable C θ hθ j y m r).aestronglyMeasurable hB

end

theorem dyadicPilotErrorField_eq_centered (n j : ℕ) (y : ℝ) (m : ℕ)
    (hdegree : m + anchoredDimension d C.order + 1 ≤ n)
    (z : ObservedSample d n) (w : CovariatePair d) :
    dyadicPilotErrorField C θ n j y m z w =
      LiftL2.centeredKernelExpansion 0 (dyadicPairKernel C θ j y m w)
        (fun i z => incrementGlobalVector j (z i) - incrementGlobalMean θ j) z :=
  (dyadicPolynomialPilot_centered_global C θ hθ n j w.1 y m (dyadicPilotRow j w.1 w.2) hdegree z).symm
end PairKernels

/-- Every L² test of the actual centered pilot error is truly L² and has
mean zero under the original sample law. -/
theorem dyadicPilotErrorField_test_moment_facts {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n j J : ℕ) (hj : j ≤ J) (y : ℝ) (hy : |y| ≤ C.holderBound) (m : ℕ)
    (hdegree : m + anchoredDimension d C.order + 1 ≤ n)
    (ν : CovariatePair d → ℝ)
    (hν : MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity))) :
    MemLp (fun z => ∫ w, ν w * dyadicPilotErrorField C θ n j y m z w
      ∂regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity)) 2 (sampleLaw θ n) ∧
    (∫ z, ∫ w, ν w * dyadicPilotErrorField C θ n j y m z w
      ∂regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity) ∂sampleLaw θ n) = 0 := by
  let := sampleLaw_isProbability C θ hθ n
  obtain ⟨hX, hmean⟩ := incrementGlobalVector_sample_facts (ℓ := C.order) C θ hθ j
  simp_rw [dyadicPilotErrorField_eq_centered C θ hθ n j y m hdegree]
  exact FieldLiftCovariance.integrated_centered_lift_moment_facts (dyadicPairKernel C θ j y m) ν
    (dyadicPairKernel_weighted_integrable C θ hθ j J hj y hy m ν hν)
    (fun i (z : ObservedSample d n) => incrementGlobalVector j (z i))
    (incrementGlobalMean θ j) hX hmean

end NearlyMinimax
