module

public import NearlyMinimax.UniformPilotDerivatives

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
    {n : ℕ} (J : ℕ) (y : ℝ) (m : ℕ → ℕ) (z : Fin n → Observation d)
    (w : Covariate d × Covariate d) : ℝ :=
  ∑ j : Fin (J + 1), dyadicPilotErrorField C θ j.val y (m j.val) z w

def dyadicMultilevelBudget (H : ℝ) (J L : ℕ) : ℝ :=
  (((2 : ℝ) ^ L)⁻¹) ^ 2 * ((2 : ℝ) ^ J) ^ 2 * H

theorem dyadicPilotRowCap_square (d ℓ j L : ℕ) (D : ℝ) :
    (dyadicPilotRowCap d ℓ j L * D) ^ 2 =
      ((anchoredDimension d ℓ : ℝ) * D) ^ 2 * (d : ℝ) *
        (((2 : ℝ) ^ L)⁻¹) ^ 2 * ((2 : ℝ) ^ j) ^ 2 := by
  simp only [dyadicPilotRowCap, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  ring

section
variable {d : ℕ} {C : ModelConstants d} [Nonempty (AnchoredIndex d C.order)] {θ : RegressionParameter d}
    (hθ : Admissible C θ)
include hθ

theorem dyadicPilotErrorField_point_moment_facts
    (n j : ℕ) {x : Covariate d} (hx : x ∈ unitCube d) (z : Covariate d)
    (y : ℝ) {m : ℕ} (hdegree : m + anchoredDimension d C.order + 1 ≤ n) :
    MemLp (fun t => dyadicPilotErrorField C θ j y m t (x, z)) 2 (sampleLaw θ n) ∧
      (∫ t, dyadicPilotErrorField C θ j y m t (x, z) ∂sampleLaw θ n) = 0 := by
  let := sampleLaw_isProbability C θ hθ n
  obtain ⟨hL2, hmean⟩ := dyadicPolynomialPilot_moment_facts hθ n j hx y
    (dyadicPilotRow j x z) hdegree
  refine ⟨hL2.sub (memLp_const _), ?_⟩
  unfold dyadicPilotErrorField
  rw [integral_sub (hL2.integrable (by norm_num)) (integrable_const _), hmean]
  simp

theorem dyadicPilotErrorField_point_second_of_variance
    {D A : ℝ} (hD : 0 < D) (hA : 0 < A)
    (hv : PilotVarianceBound C θ D A) :
    ∀ n j L : ℕ, j ≤ L → ∀ x ∈ unitCube d, ∀ z ∈ unitCube d,
      dyadicGridLabel L x =
        dyadicGridLabel L z →
      ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m : ℕ,
      m + anchoredDimension d C.order + 1 ≤ n → ∀ Λ : ℝ, 0 < Λ →
      Λ ≤ (n : ℝ) - (m + anchoredDimension d C.order + 1) + 1 →
      (∫ t, dyadicPilotErrorField C θ j y m t (x, z) ^ 2 ∂sampleLaw θ n) ≤
        (dyadicPilotRowCap d C.order j L * D) ^ 2 * dyadicPilotSeries C A Λ j m := by
  intro n j L hj x hx z hz hc y hy m hdegree Λ hΛ hΛn
  obtain ⟨hL2, hmean⟩ := dyadicPolynomialPilot_moment_facts hθ n j hx y
    (dyadicPilotRow j x z) hdegree
  have h := hv n j x hx y hy m (dyadicPilotRow j x z) hdegree Λ hΛ hΛn
  rw [variance_eq_integral hL2.aemeasurable, hmean] at h
  have hr := dyadicPilotRow_sum_abs_le_fine_cell (ℓ := C.order) hj hx hz hc.symm
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (dyadicPilotSeries_nonneg C A Λ hΛ.le _ _)
  apply pow_le_pow_left₀ (mul_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hD.le)
  exact mul_le_mul_of_nonneg_right hr hD.le

end

variable {d : ℕ} {C : ModelConstants d} [Nonempty (AnchoredIndex d C.order)] {θ : RegressionParameter d}
    (hθ : Admissible C θ) {n J : ℕ} {x : Covariate d} (hx : x ∈ unitCube d) {L : ℕ} (hJL : J ≤ L) {y : ℝ}
    (hy : |y| ≤ C.holderBound) {m : ℕ → ℕ}
    (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n)
    {ν : Covariate d × Covariate d → ℝ}
    (hν : MemLp ν 2 (dyadicPairDesignMeasure θ L))
include hθ

include hx in
theorem dyadicMultilevelErrorField_point_moment_facts (z : Covariate d)
    (y : ℝ) {m : ℕ → ℕ}
    (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n) :
    MemLp (fun t => dyadicMultilevelErrorField C θ J y m t (x, z)) 2 (sampleLaw θ n) ∧
      (∫ t, dyadicMultilevelErrorField C θ J y m t (x, z) ∂sampleLaw θ n) = 0 := by
  let := sampleLaw_isProbability C θ hθ n
  have hf (j : Fin (J + 1)) := dyadicPilotErrorField_point_moment_facts hθ n j.val hx z y (hdegree j)
  refine ⟨memLp_finsetSum _ (fun j _ => (hf j).1), ?_⟩
  unfold dyadicMultilevelErrorField
  rw [integral_finsetSum Finset.univ (fun j _ => (hf j).1.integrable (by norm_num))]
  exact Finset.sum_eq_zero (fun j _ => (hf j).2)

theorem dyadicPilotErrorField_weighted_integrable {j L : ℕ} (hj : j ≤ L) {y : ℝ} (hy : |y| ≤ C.holderBound) {m : ℕ}
    (hdegree : m + anchoredDimension d C.order + 1 ≤ n)
    {ν : Covariate d × Covariate d → ℝ}
    (hν : MemLp ν 2 (dyadicPairDesignMeasure θ L))
    (t : Fin n → Observation d) :
    Integrable (fun w => ν w * dyadicPilotErrorField C θ j y m t w)
      (dyadicPairDesignMeasure θ L) := by
  let M := dyadicPairDesignMeasure θ L
  let := regularPairDesignMeasure_isFinite hθ ((2 : ℕ) ^ L) (by positivity)
  let R := m + anchoredDimension d C.order + 1
  let H (w : Covariate d × Covariate d) (r : Fin R) :=
    dyadicIncrementKernel (C := C) θ j w.1 y m (dyadicPilotRow j w.1 w.2) (r.val + 1)
  let X (i : Fin n) (z : Fin n → Observation d) :=
    incrementGlobalVector (ℓ := C.order) j (z i) - incrementGlobalMean θ j
  have hc  :=
    (regularPairDesignMeasure_cube_ae hθ ((2 : ℕ) ^ L) (by positivity)).mono (fun w hw => hw.1)
  have hrow := dyadicPilotRow_pair_cap (ℓ := C.order) hθ hj
  have hH (r : Fin R)  :=
    dyadicIncrementKernel_weighted_integrable hθ j hy m (r.val + 1)
      (dyadicPilotRow_field_measurable j)
      (dyadicPilotRowCap_nonneg _ _ _ _) hc hrow hν
  have hi := integrable_finsetSum Finset.univ (fun r _ =>
    FieldLiftCovariance.weighted_kernel_statistic_integrable X (hH r) t)
  have heq : (fun w => ν w * dyadicPilotErrorField C θ j y m t w) =
      (fun w => ∑ r : Fin R, ν w * LiftL2.kernelStatistic (H w r) X t) := by
    funext w
    unfold dyadicPilotErrorField
    rw [← dyadicPolynomialPilot_centered_global hθ n j w.1 y
      (dyadicPilotRow j w.1 w.2) hdegree t]
    simp [LiftL2.centeredKernelExpansion, zero_add, Finset.mul_sum]
    rfl
  rwa [heq]

include hJL hy hdegree hν in
theorem dyadicMultilevelErrorField_test_integral_sum
    (t : Fin n → Observation d) :
    (∫ w, ν w * dyadicMultilevelErrorField C θ J y m t w
      ∂dyadicPairDesignMeasure θ L) =
    ∑ j : Fin (J + 1), ∫ w, ν w * dyadicPilotErrorField C θ j.val y (m j.val) t w
      ∂dyadicPairDesignMeasure θ L := by
  unfold dyadicMultilevelErrorField
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum Finset.univ (fun j _ =>
    dyadicPilotErrorField_weighted_integrable hθ
      ((Nat.le_of_lt_succ j.isLt).trans hJL) hy (hdegree j) hν t)

include hJL hy hdegree hν in
theorem dyadicMultilevelErrorField_test_moment_facts :
    MemLp (fun t => ∫ w, ν w * dyadicMultilevelErrorField C θ J y m t w
      ∂dyadicPairDesignMeasure θ L) 2 (sampleLaw θ n) ∧
    (∫ t, ∫ w, ν w * dyadicMultilevelErrorField C θ J y m t w
      ∂dyadicPairDesignMeasure θ L ∂sampleLaw θ n) = 0 := by
  let := sampleLaw_isProbability C θ hθ n
  have hf (j : Fin (J + 1)) := dyadicPilotErrorField_test_moment_facts hθ
    ((Nat.le_of_lt_succ j.isLt).trans hJL) hy (hdegree j) hν
  simp_rw [dyadicMultilevelErrorField_test_integral_sum hθ hJL hy hdegree hν]
  refine ⟨memLp_finsetSum _ (fun j _ => (hf j).1), ?_⟩
  rw [integral_finsetSum Finset.univ (fun j _ => (hf j).1.integrable (by norm_num))]
  exact Finset.sum_eq_zero (fun j _ => (hf j).2)

theorem dyadicMultilevelErrorField_joint_measurable (y : ℝ) {m : ℕ → ℕ}
    (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n) :
    Measurable (fun t : (Fin n → Observation d) × (Covariate d × Covariate d) =>
      dyadicMultilevelErrorField C θ J y m t.1 t.2) := by
  have hm := Finset.measurable_sum Finset.univ (fun j _ =>
    dyadicPolynomialPilot_centered_field_measurable hθ n j.val y (dyadicPilotRow_field_measurable j.val) (hdegree j))
  assumption

end NearlyMinimax
