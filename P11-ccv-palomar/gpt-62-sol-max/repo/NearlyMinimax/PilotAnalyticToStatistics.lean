module

public import NearlyMinimax.PilotCommonBounds


@[expose] public section

/-! Actual statistical consequences of a genuine population derivative bound.
The endpoint below will discharge its analytic input uniformly over domains. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix MvPolynomial
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

section
variable {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (D A : ℝ) (hD : 0 < D) (hA : 0 < A)
include hθ hD hA

def DyadicRawKernelBudget : Prop :=
    ∀ n j : ℕ,
      ∀ x ∈ unitCube d, ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m k : ℕ,
      ∀ row : Fin (anchoredDimension d C.order) → ℝ, ∀ hk : k ≤ n,
      ∀ Λ : ℝ, 0 < Λ →
        (((k.factorial : ℝ) * Λ ^ k)⁻¹) *
          (∫ z : ObservedSample d n,
            dyadicIncrementKernel C θ j x y m row k
              (fun i => incrementGlobalVector j (z (Fin.castLEEmb hk i))) ^ 2 ∂sampleLaw θ n) ≤
          ((∑ i, |row i|) * D) ^ 2 * (k.factorial : ℝ) *
            (A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d C.order)) *
              preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j) / Λ) ^ k

theorem dyadicIncrementKernel_raw_budget_of_derivative
    (hder : DyadicRowDerivativeBound C θ C.holderBound D A) :
    DyadicRawKernelBudget C θ D A := by
  intro n j x hx y hy m k row hk Λ hΛ
  let := sampleLaw_isProbability C θ hθ n
  obtain ⟨hX, hmean⟩ := dyadicIncrementRawVector_sample_facts C θ hθ j x hx
  let X (i : Fin n) (z : Fin n → Observation d) := dyadicIncrementRawVector (ℓ := C.order) j x (z i)
  let e := Fin.castLEEmb hk
  let E := (Fintype.card (incrementVariables (anchoredDimension d C.order)) : ℝ) *
    preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j
  have hE : 0 ≤ E := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (preconditionedPilotMomentConstant_pos C _).le)
      (dyadicPilotScale_pos _ _).le
  have hb := KernelMomentBounds.factorial_kernel_budget
    (iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
      C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row) (dyadicIncrementRawMean θ j x))
    (fun i => X (e i)) (hX.toIndependentL2.precomp e) E ((∑ i, |row i|) * D) A Λ hE hΛ
    (fun i => dyadicIncrementRawVector_sample_second_le C θ hθ j x hx (e i))
    (hder j x hx y hy m k row)
  simpa only [dyadicIncrementKernel_raw, E, X, e] using hb


section
variable (n j L : ℕ) (hj : j ≤ L) (y : ℝ) (hy : |y| ≤ C.holderBound) (m : ℕ)
    (hdegree : m + anchoredDimension d C.order + 1 ≤ n)
    (Λ : ℝ) (hΛ : 0 < Λ) (hΛn : Λ ≤ (n : ℝ) - (m + anchoredDimension d C.order + 1) + 1)
    (hraw : DyadicRawKernelBudget C θ D A)

local notation "P" => (dyadicPilotRowCap d C.order j L * D) ^ 2 * dyadicPilotSeries C A Λ j m
local notation "μₙ" => sampleLaw θ n
local notation "ℳ" => regularPairDesignMeasure θ (2 ^ L) (Nat.two_pow_pos L)
local notation "E" => dyadicPilotErrorField C θ n j y m

private def dyadicPairKernelEnergy (w : CovariatePair d) : ℝ :=
  ∑ r : Fin (m + anchoredDimension d C.order + 1),
    (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹ *
      ∫ z, dyadicPairKernel C θ j y m w r (fun i =>
        incrementGlobalVector j (z (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hdegree) i))) ^ 2 ∂μₙ

include hy hΛ hraw in
private theorem dyadicPairKernelEnergy_le (w : CovariatePair d) (hw : w.1 ∈ unitCube d)
    (hr : (∑ i, |dyadicPilotRow (ℓ := C.order) j w.1 w.2 i|) ≤ dyadicPilotRowCap d C.order j L) :
    dyadicPairKernelEnergy C θ n j y m hdegree Λ w ≤ P := by
  have hs := dyadicPilotSeries_nonneg C A Λ hΛ.le j m
  refine le_trans (b := ((∑ i, |dyadicPilotRow (ℓ := C.order) j w.1 w.2 i|) * D)^2 *
      dyadicPilotSeries C A Λ j m) ?_ (by gcongr)
  unfold dyadicPairKernelEnergy dyadicPilotSeries
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun r _ => by
    simpa only [dyadicPairKernel, mul_assoc] using
      hraw n j w.1 hw y hy m (r.val + 1) (dyadicPilotRow j w.1 w.2)
        ((Nat.succ_le_of_lt r.isLt).trans hdegree) Λ hΛ

include hraw hy hΛ hΛn hj hdegree in
/-- Pointwise energy uses the same factorial kernel series as localized tests. -/
theorem dyadicPilotErrorField_point_energy
    (x : Covariate d) (hx : x ∈ unitCube d) (z : Covariate d) (hz : z ∈ unitCube d)
    (hc : regularGridCell (2 ^ L) (by positivity) x = regularGridCell (2 ^ L) (by positivity) z) :
    MemLp (fun t => E t (x, z)) 2 μₙ ∧ (∫ t, E t (x, z) ^ 2 ∂μₙ) ≤ P := by
  let := sampleLaw_isProbability C θ hθ n
  have hf := dyadicPilotErrorField_point_moment_facts C θ hθ n j x hx z y m hdegree
  refine ⟨hf.1, ?_⟩
  rw [← variance_of_integral_eq_zero hf.1.aemeasurable hf.2]
  simp_rw [dyadicPilotErrorField_eq_centered C θ hθ n j y m hdegree]
  obtain ⟨hX, hmean⟩ := incrementGlobalVector_sample_facts (ℓ := C.order) C θ hθ j
  have h := LiftL2.centered_expansion_variance_le_raw_power 0 (dyadicPairKernel C θ j y m (x, z))
    (fun r => dyadicIncrementKernel_symmetric C θ j x y m (dyadicPilotRow j x z) (r.val + 1))
    (fun i (t : ObservedSample d n) => incrementGlobalVector j (t i)) (incrementGlobalMean θ j)
    hdegree hX hmean Λ hΛ (by simpa using hΛn)
  exact h.trans (dyadicPairKernelEnergy_le C θ hθ D A hD hA n j L y hy m hdegree Λ hΛ hraw
    (x, z) hx (dyadicPilotRow_sum_abs_le_fine_cell j L hj x z hx hz hc.symm))

include hj hy hΛ hΛn hraw hdegree in
theorem dyadicPilotErrorField_test_energy
    (ν : CovariatePair d → ℝ) (hν : MemLp ν 2 ℳ) :
    MemLp (fun z => ∫ w, ν w * E z w ∂ℳ) 2 μₙ ∧
      (∫ z, (∫ w, ν w * E z w ∂ℳ) ^ 2 ∂μₙ) ≤
        (C.densityUpper ^ 2 / dyadicPilotScale d (j - 1)) * P * (∫ w, ν w ^ 2 ∂ℳ) := by
  let := sampleLaw_isProbability C θ hθ n
  have hf := dyadicPilotErrorField_test_moment_facts C θ hθ n j L hj y hy m hdegree ν hν
  refine ⟨hf.1, ?_⟩
  rw [← variance_of_integral_eq_zero hf.1.aemeasurable hf.2]
  let := regularPairDesignMeasure_isFinite C θ hθ ((2 : ℕ) ^ L) (by positivity)
  let R := m + anchoredDimension d C.order + 1
  let X (i : Fin n) (z : ObservedSample d n) := incrementGlobalVector (ℓ := C.order) j (z i)
  let H := dyadicPairKernel C θ j y m
  have hcube := (regularPairDesignMeasure_cube_ae C θ hθ (2 ^ L) (by positivity)).mono fun _ hw => hw.1
  have hrow := dyadicPilotRow_pair_cap (ℓ := C.order) C θ hθ j L hj
  obtain ⟨hX, hmean⟩ := incrementGlobalVector_sample_facts (ℓ := C.order) C θ hθ j
  let e (r : Fin R) := Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hdegree)
  let Op (r : Fin R) := FieldLiftCovariance.rawKernelOperator (e r) X hX.toIndependentL2
  choose B hBpos hBcap using dyadicPairKernel_bounded C θ hθ j L hj y hy m
  have hopcap (r : Fin R) : ∀ᵐ w ∂ℳ, ‖Op r (H w r)‖ ≤ ‖Op r‖ * B r := by
    filter_upwards [hBcap r] with w hw
    exact ((Op r).le_opNorm _).trans (mul_le_mul_of_nonneg_left hw (norm_nonneg _))
  have hblock (c : Fin (Fintype.card (DyadicPilotLabelIndex d (j - 1)))) :
      (ℳ).real {w | dyadicPilotLabel (j - 1) w.1 = c} ≤ C.densityUpper ^ 2 / dyadicPilotScale d (j - 1) := by
    have hs : {w : CovariatePair d | dyadicPilotLabel (j - 1) w.1 = c} =
        {w | regularGridCell ((2 : ℕ) ^ (j - 1)) (by positivity) w.1 =
          (Fintype.equivFin (DyadicPilotLabelIndex d (j - 1))).symm c} := by
      ext w
      exact (Fintype.equivFin (DyadicPilotLabelIndex d (j - 1))).apply_eq_iff_eq_symm_apply
    rw [hs]
    apply regularPairDesignMeasure_parent_block_mass <;> assumption
  have hu := FieldLiftCovariance.integrated_centered_lift_variance_localized
    (μ := sampleLaw θ n) (M := ℳ) (n := n)
    (p := Fintype.card (IncrementGlobalIndex d C.order j)) (R := R)
    (q := Fintype.card (DyadicPilotLabelIndex d (j - 1))) H ν hν (dyadicPairKernel_weighted_integrable C θ hθ j L hj y hy m ν hν)
    (fun r => (dyadicPairKernel_measurable C θ hθ j y m r).aestronglyMeasurable)
    (fun w r σ v => dyadicIncrementKernel_symmetric C θ j w.1 y m (dyadicPilotRow j w.1 w.2) _ σ v)
    X (incrementGlobalMean θ j) hdegree hX hmean Λ hΛ
    (by simpa only [R, Nat.cast_add, Nat.cast_one] using hΛn)
    (fun w => dyadicPilotLabel (j - 1) w.1) ((dyadicPilotLabel_measurable _).comp measurable_fst)
    (fun r => ‖Op r‖ * B r) (fun r => mul_nonneg (norm_nonneg (Op r)) (hBpos r).le) hopcap
    (fun r w v hv => Filter.Eventually.of_forall (fun z =>
      dyadicIncrementKernel_disjoint C θ j (r.val + 1) (by omega) w.1 v.1 hv y y m m
        (dyadicPilotRow j w.1 w.2) (dyadicPilotRow j v.1 v.2) (fun i => z (e r i))))
    (C.densityUpper ^ 2 / dyadicPilotScale d (j - 1)) hblock
  let S := dyadicPairKernelEnergy C θ n j y m hdegree Λ
  have hSbound : ∀ᵐ w ∂ℳ, S w ≤ P := by
    filter_upwards [hcube, hrow] with w hw hr
    exact dyadicPairKernelEnergy_le C θ hθ D A hD hA n j L y hy m hdegree Λ hΛ hraw w hw hr
  have hSnon (w) : 0 ≤ S w := by unfold S dyadicPairKernelEnergy; positivity
  have hile := integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => mul_nonneg (sq_nonneg (ν w)) (hSnon w))
    (hν.integrable_sq.const_mul P)
    (hSbound.mono (fun w hw => (mul_le_mul_of_nonneg_left hw (sq_nonneg (ν w))).trans_eq (mul_comm _ _)))
  rw [integral_const_mul] at hile
  simp_rw [dyadicPilotErrorField_eq_centered C θ hθ n j y m hdegree]
  have hL : 0 ≤ C.densityUpper ^ 2 / dyadicPilotScale d (j - 1) :=
    div_nonneg (sq_nonneg _) (dyadicPilotScale_pos _ _).le
  exact hu.trans (by simpa only [S, dyadicPairKernelEnergy, H, X, R, mul_assoc] using mul_le_mul_of_nonneg_left hile hL)

end
end

end NearlyMinimax
