module

public import NearlyMinimax.DyadicPilotWeakTests
public import NearlyMinimax.PilotMultilevelCore
public import NearlyMinimax.PilotSeriesEnvelope
public import NearlyMinimax.DyadicPilotFieldMeasurability

@[expose] public section

/-! Actual multilevel pilot errors, their mean and pointwise energy, and
their universal covariance under the original pair design measure. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def dyadicMultilevelErrorField {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (n J : ℕ) (y : ℝ) (m : ℕ → ℕ) (z : Fin n → Observation d)
    (w : Covariate d × Covariate d) : ℝ :=
  ∑ j : Fin (J + 1), dyadicPilotErrorField C θ n j.val y (m j.val) z w

def dyadicMultilevelBudget (H : ℝ) (J L : ℕ) : ℝ :=
  (((2 : ℝ) ^ L)⁻¹) ^ 2 * ((2 : ℝ) ^ J) ^ 2 * H

theorem dyadicPilotRowCap_square (d ℓ j L : ℕ) (D : ℝ) :
    (dyadicPilotRowCap d ℓ j L * D) ^ 2 =
      ((anchoredDimension d ℓ : ℝ) * D) ^ 2 * (d : ℝ) *
        (((2 : ℝ) ^ L)⁻¹) ^ 2 * ((2 : ℝ) ^ j) ^ 2 := by
  simp only [dyadicPilotRowCap, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  ring

theorem dyadicPilotErrorField_point_moment_facts {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n j : ℕ) (x : Covariate d) (hx : x ∈ unitCube d) (z : Covariate d)
    (y : ℝ) (m : ℕ) (hdegree : m + anchoredDimension d C.order + 1 ≤ n) :
    MemLp (fun t => dyadicPilotErrorField C θ n j y m t (x, z)) 2 (sampleLaw θ n) ∧
      (∫ t, dyadicPilotErrorField C θ n j y m t (x, z) ∂sampleLaw θ n) = 0 := by
  let := sampleLaw_isProbability C θ hθ n
  obtain ⟨hL2, hmean⟩ := dyadicPolynomialPilot_moment_facts C θ hθ n j x hx y m
    (dyadicPilotRow j x z) hdegree
  refine ⟨hL2.sub (memLp_const _), ?_⟩
  unfold dyadicPilotErrorField
  rw [integral_sub (hL2.integrable (by norm_num)) (integrable_const _), hmean]
  simp

theorem dyadicMultilevelErrorField_point_moment_facts {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n J : ℕ) (x : Covariate d) (hx : x ∈ unitCube d) (z : Covariate d)
    (y : ℝ) (m : ℕ → ℕ)
    (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n) :
    MemLp (fun t => dyadicMultilevelErrorField C θ n J y m t (x, z)) 2 (sampleLaw θ n) ∧
      (∫ t, dyadicMultilevelErrorField C θ n J y m t (x, z) ∂sampleLaw θ n) = 0 := by
  let := sampleLaw_isProbability C θ hθ n
  have hf (j : Fin (J + 1)) := dyadicPilotErrorField_point_moment_facts C θ hθ n j.val x hx z y
    (m j.val) (hdegree j)
  refine ⟨memLp_finsetSum _ (fun j _ => (hf j).1), ?_⟩
  unfold dyadicMultilevelErrorField
  rw [integral_finsetSum Finset.univ (fun j _ => (hf j).1.integrable (by norm_num))]
  exact Finset.sum_eq_zero (fun j _ => (hf j).2)

theorem dyadicPilotErrorField_weighted_integrable {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n j L : ℕ) (hj : j ≤ L) (y : ℝ) (hy : |y| ≤ C.holderBound) (m : ℕ)
    (hdegree : m + anchoredDimension d C.order + 1 ≤ n)
    (ν : Covariate d × Covariate d → ℝ)
    (hν : MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)))
    (t : Fin n → Observation d) :
    Integrable (fun w => ν w * dyadicPilotErrorField C θ n j y m t w)
      (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) := by
  let M := regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)
  let := regularPairDesignMeasure_isFinite C θ hθ ((2 : ℕ) ^ L) (by positivity)
  let R := m + anchoredDimension d C.order + 1
  let H (w : Covariate d × Covariate d) (r : Fin R) :=
    dyadicIncrementKernel C θ j w.1 y m (dyadicPilotRow j w.1 w.2) (r.val + 1)
  let X (i : Fin n) (z : Fin n → Observation d) :=
    incrementGlobalVector (ℓ := C.order) j (z i) - incrementGlobalMean θ j
  have hc : ∀ᵐ w ∂M, w.1 ∈ unitCube d :=
    (regularPairDesignMeasure_cube_ae C θ hθ ((2 : ℕ) ^ L) (by positivity)).mono (fun w hw => hw.1)
  have hrow := dyadicPilotRow_pair_cap (ℓ := C.order) C θ hθ j L hj
  have hH (r : Fin R) : Integrable (fun w => ν w • H w r) M :=
    dyadicIncrementKernel_weighted_integrable C θ hθ j y hy m (r.val + 1) _
      (dyadicPilotRow_field_measurable j) M (dyadicPilotRowCap d C.order j L)
      (dyadicPilotRowCap_nonneg _ _ _ _) hc hrow ν hν
  have hi := integrable_finsetSum Finset.univ (fun r _ =>
    FieldLiftCovariance.weighted_kernel_statistic_integrable X ν (fun w => H w r) (hH r) t)
  have heq : (fun w => ν w * dyadicPilotErrorField C θ n j y m t w) =
      (fun w => ∑ r : Fin R, ν w * LiftL2.kernelStatistic (H w r) X t) := by
    funext w
    unfold dyadicPilotErrorField
    rw [← dyadicPolynomialPilot_centered_global C θ hθ n j w.1 y m
      (dyadicPilotRow j w.1 w.2) hdegree t]
    simp only [LiftL2.centeredKernelExpansion, zero_add, Finset.mul_sum]
    rfl
  rwa [heq]

theorem dyadicMultilevelErrorField_test_integral_sum {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n J L : ℕ) (hJL : J ≤ L) (y : ℝ) (hy : |y| ≤ C.holderBound) (m : ℕ → ℕ)
    (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n)
    (ν : Covariate d × Covariate d → ℝ)
    (hν : MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)))
    (t : Fin n → Observation d) :
    (∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w
      ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) =
    ∑ j : Fin (J + 1), ∫ w, ν w * dyadicPilotErrorField C θ n j.val y (m j.val) t w
      ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity) := by
  unfold dyadicMultilevelErrorField
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum Finset.univ (fun j _ =>
    dyadicPilotErrorField_weighted_integrable C θ hθ n j.val L
      ((Nat.le_of_lt_succ j.isLt).trans hJL) y hy (m j.val) (hdegree j) ν hν t)

theorem dyadicMultilevelErrorField_test_moment_facts {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n J L : ℕ) (hJL : J ≤ L) (y : ℝ) (hy : |y| ≤ C.holderBound) (m : ℕ → ℕ)
    (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n)
    (ν : Covariate d × Covariate d → ℝ)
    (hν : MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity))) :
    MemLp (fun t => ∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w
      ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) 2 (sampleLaw θ n) ∧
    (∫ t, ∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w
      ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity) ∂sampleLaw θ n) = 0 := by
  let := sampleLaw_isProbability C θ hθ n
  have hf (j : Fin (J + 1)) := dyadicPilotErrorField_test_moment_facts C θ hθ n j.val L
    ((Nat.le_of_lt_succ j.isLt).trans hJL) y hy (m j.val) (hdegree j) ν hν
  simp_rw [dyadicMultilevelErrorField_test_integral_sum C θ hθ n J L hJL y hy m hdegree ν hν]
  refine ⟨memLp_finsetSum _ (fun j _ => (hf j).1), ?_⟩
  rw [integral_finsetSum Finset.univ (fun j _ => (hf j).1.integrable (by norm_num))]
  exact Finset.sum_eq_zero (fun j _ => (hf j).2)

theorem dyadicMultilevelErrorField_joint_measurable {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n J : ℕ) (y : ℝ) (m : ℕ → ℕ)
    (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n) :
    Measurable (fun t : (Fin n → Observation d) × (Covariate d × Covariate d) =>
      dyadicMultilevelErrorField C θ n J y m t.1 t.2) := by
  have hm := Finset.measurable_sum Finset.univ (fun (j : Fin (J + 1)) _ =>
    dyadicPolynomialPilot_centered_field_measurable C θ hθ n j.val y (m j.val)
      (fun w => dyadicPilotRow j.val w.1 w.2) (dyadicPilotRow_field_measurable j.val) (hdegree j))
  convert hm using 1
  funext t
  simp only [dyadicMultilevelErrorField]
  rfl

end NearlyMinimax
