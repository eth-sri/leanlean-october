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
    (n J : ℕ) (y : ℝ) (m : ℕ → ℕ) (z : ObservedSample d n)
    (w : CovariatePair d) : ℝ :=
  ∑ j : Fin (J + 1), dyadicPilotErrorField C θ n j.val y (m j.val) z w

def dyadicMultilevelBudget (H : ℝ) (J L : ℕ) : ℝ :=
  (((2 : ℝ) ^ L)⁻¹) ^ 2 * ((2 : ℝ) ^ J) ^ 2 * H

theorem dyadicPilotRowCap_square (d ℓ j L : ℕ) (D : ℝ) :
    (dyadicPilotRowCap d ℓ j L * D) ^ 2 =
      ((anchoredDimension d ℓ : ℝ) * D) ^ 2 * (d : ℝ) *
        (((2 : ℝ) ^ L)⁻¹) ^ 2 * ((2 : ℝ) ^ j) ^ 2 := by
  simp only [dyadicPilotRowCap, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  ring

private theorem centered_sum_memLp {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsFiniteMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ j, MemLp (X j) 2 μ ∧ (∫ t, X j t ∂μ) = 0) :
    MemLp (fun t => ∑ j, X j t) 2 μ ∧ (∫ t, ∑ j, X j t ∂μ) = 0 := by
  refine ⟨memLp_finsetSum _ (fun j _ => (hX j).1), ?_⟩
  rw [integral_finsetSum Finset.univ (fun j _ => (hX j).1.integrable (by norm_num))]
  exact Finset.sum_eq_zero (fun j _ => (hX j).2)

section
variable {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)]

section
variable (θ : RegressionParameter d) (hθ : Admissible C θ)
include hθ

theorem dyadicPilotErrorField_point_moment_facts
    (n j : ℕ) (x : Covariate d) (hx : x ∈ unitCube d) (z : Covariate d)
    (y : ℝ) (m : ℕ) (hdegree : m + anchoredDimension d C.order + 1 ≤ n) :
    MemLp (fun t => dyadicPilotErrorField C θ n j y m t (x, z)) 2 (sampleLaw θ n) ∧
      (∫ t, dyadicPilotErrorField C θ n j y m t (x, z) ∂sampleLaw θ n) = 0 := by
  let := sampleLaw_isProbability C θ hθ n
  obtain ⟨hL2, hmean⟩ := dyadicPolynomialPilot_moment_facts C θ hθ n j x hx y m
    (dyadicPilotRow j x z) hdegree
  refine ⟨hL2.sub (memLp_const _), ?_⟩
  unfold dyadicPilotErrorField
  simp [integral_sub (hL2.integrable (by norm_num)) (integrable_const _), hmean]

theorem dyadicMultilevelErrorField_point_moment_facts
    (n J : ℕ) (x : Covariate d) (hx : x ∈ unitCube d) (z : Covariate d)
    (y : ℝ) (m : ℕ → ℕ)
    (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n) :
    MemLp (fun t => dyadicMultilevelErrorField C θ n J y m t (x, z)) 2 (sampleLaw θ n) ∧
      (∫ t, dyadicMultilevelErrorField C θ n J y m t (x, z) ∂sampleLaw θ n) = 0 := by
  let := sampleLaw_isProbability C θ hθ n
  exact centered_sum_memLp _ fun j => dyadicPilotErrorField_point_moment_facts C θ hθ n j.val x hx z y
    (m j.val) (hdegree j)

theorem dyadicPilotErrorField_weighted_integrable
    (n j L : ℕ) (hj : j ≤ L) (y : ℝ) (hy : |y| ≤ C.holderBound) (m : ℕ)
    (hdegree : m + anchoredDimension d C.order + 1 ≤ n)
    (ν : CovariatePair d → ℝ)
    (hν : MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)))
    (t : ObservedSample d n) :
    Integrable (fun w => ν w * dyadicPilotErrorField C θ n j y m t w)
      (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) := by
  simp_rw [dyadicPilotErrorField_eq_centered C θ hθ n j y m hdegree,
    LiftL2.centeredKernelExpansion, zero_add, Finset.mul_sum]
  exact integrable_finsetSum Finset.univ fun r _ =>
    FieldLiftCovariance.weighted_kernel_statistic_integrable
      (fun i (z : ObservedSample d n) => incrementGlobalVector j (z i) - incrementGlobalMean θ j) ν
      (fun w => dyadicPairKernel C θ j y m w r)
      (dyadicPairKernel_weighted_integrable C θ hθ j L hj y hy m ν hν r) t

section
variable (n J L : ℕ) (hJL : J ≤ L) (y : ℝ) (hy : |y| ≤ C.holderBound) (m : ℕ → ℕ)
    (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n)
    (ν : CovariatePair d → ℝ)
    (hν : MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)))
include hJL hy hdegree hν

theorem dyadicMultilevelErrorField_test_integral_sum
    (t : ObservedSample d n) :
    (∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w
      ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) =
    ∑ j : Fin (J + 1), ∫ w, ν w * dyadicPilotErrorField C θ n j.val y (m j.val) t w
      ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity) := by
  unfold dyadicMultilevelErrorField
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum Finset.univ (fun j _ =>
    dyadicPilotErrorField_weighted_integrable C θ hθ n j.val L
      ((Nat.le_of_lt_succ j.isLt).trans hJL) y hy (m j.val) (hdegree j) ν hν t)

theorem dyadicMultilevelErrorField_test_moment_facts :
    MemLp (fun t => ∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w
      ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) 2 (sampleLaw θ n) ∧
    (∫ t, ∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w
      ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity) ∂sampleLaw θ n) = 0 := by
  simp_rw [dyadicMultilevelErrorField_test_integral_sum C θ hθ n J L hJL y hy m hdegree ν hν]
  let := sampleLaw_isProbability C θ hθ n
  exact centered_sum_memLp _ fun j => dyadicPilotErrorField_test_moment_facts C θ hθ n j.val L
    ((Nat.le_of_lt_succ j.isLt).trans hJL) y hy (m j.val) (hdegree j) ν hν

end

theorem dyadicMultilevelErrorField_joint_measurable
    (n J : ℕ) (y : ℝ) (m : ℕ → ℕ)
    (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n) :
    Measurable (fun t : ObservedSample d n × (CovariatePair d) =>
      dyadicMultilevelErrorField C θ n J y m t.1 t.2) := by
  have hm := Finset.measurable_sum Finset.univ (fun (j : Fin (J + 1)) _ =>
    dyadicPolynomialPilot_centered_field_measurable C θ hθ n j.val y (m j.val)
      (fun w => dyadicPilotRow j.val w.1 w.2) (dyadicPilotRow_field_measurable j.val) (hdegree j))
  assumption

end

end

end NearlyMinimax
