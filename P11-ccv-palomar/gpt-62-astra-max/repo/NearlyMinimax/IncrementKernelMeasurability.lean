module

public import NearlyMinimax.UniformPilotDerivatives

public import NearlyMinimax.IncrementPilotKernels
public import NearlyMinimax.IncrementCoordinateBounds


@[expose] public section

/-! Joint Borel derivative coefficient fields for actual dyadic pilots. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

section
variable {p r q k : ℕ} {F : Type*}

instance finiteInputMultilinearMeasurableSpace
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    MeasurableSpace (ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) F) := borel _

instance finiteInputMultilinearBorelSpace
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    BorelSpace (ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) F) := ⟨rfl⟩

instance finiteInputScalarMultilinearFiniteDimensional (p k : ℕ) :
    FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) ℝ) := by
  let e : (ContinuousMultilinearMap ℝ (fun _ => Fin p → ℝ) ℝ) →L[ℝ]
      ((Fin k → Fin p) → ℝ) := ContinuousLinearMap.pi (fun σ =>
    ContinuousMultilinearMap.apply ℝ (fun _ => Fin p → ℝ) ℝ
      (fun i => Pi.single (σ i) 1))
  apply FiniteDimensional.of_injective e.toLinearMap
  intro H G he
  ext v
  change H.toMultilinearMap v = G.toMultilinearMap v
  rw [LiftL2.multilinear_coordinate_expansion H.toMultilinearMap,
    LiftL2.multilinear_coordinate_expansion G.toMultilinearMap]
  apply Finset.sum_congr rfl
  intro σ _
  have hc := congrFun he σ
  change H (fun i => Pi.single (σ i) 1) = G (fun i => Pi.single (σ i) 1) at hc
  exact congrArg (fun a => a * ∏ i, v i (σ i)) hc

theorem rowFunctional_continuous : Continuous (rowFunctional (r := r)) := continuous_finset_sum Finset.univ (fun i _ => (continuous_apply i).smul continuous_const)

theorem continuous_row_postcompose :
    Continuous (fun z : (Fin r → ℝ) ×
      ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) (Fin r → ℝ) =>
        (rowFunctional z.1).compContinuousMultilinearMap z.2) := ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => Fin p → ℝ)
    (Fin r → ℝ) ℝ).continuous.comp (rowFunctional_continuous.comp continuous_fst)).clm_apply continuous_snd

theorem continuous_multilinear_pullback :
    Continuous (fun z :
      ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) ℝ ×
        ((Fin q → ℝ) →L[ℝ] (Fin p → ℝ)) =>
        z.1.compContinuousLinearMap (fun _ => z.2)) := ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ => Fin q → ℝ) (fun _ : Fin k => Fin p → ℝ) ℝ).cont.comp
    (continuous_pi (fun _ => continuous_snd))).clm_apply continuous_fst

end

variable {d : ℕ} {C : ModelConstants d} [Nonempty (AnchoredIndex d C.order)] {θ : RegressionParameter d}
    (hθ : Admissible C θ) (j : ℕ) {y : ℝ} (hy : |y| ≤ C.holderBound) (m k : ℕ)
    {row : Covariate d × Covariate d → Fin (anchoredDimension d C.order) → ℝ} (hrowMeas : Measurable row)
    {M : Measure (Covariate d × Covariate d)}
include hθ

/-- The anchor and arbitrary measurable physical row determine a Borel
global derivative field under the original admissible population law. -/
theorem dyadicIncrementKernel_field_measurable (y : ℝ) (m k : ℕ)
    {row : Covariate d × Covariate d → Fin (anchoredDimension d C.order) → ℝ}
    (hrow : Measurable row) :
    Measurable (fun w =>
      dyadicIncrementKernel θ j w.1 y m (row w) k) := by
  have hm : Measurable (fun w : Covariate d × Covariate d =>
      dyadicIncrementRawMean θ j w.1) :=
    (dyadicIncrementRawMean_measurable (ℓ := C.order) hθ j).comp measurable_fst
  have hD := ((incrementFinVector_contDiff (anchoredDimension d C.order)
    C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m).continuous_iteratedFDeriv
      (show (k : WithTop ℕ∞) ≤ ⊤ from le_top)).measurable.comp hm
  have hscalar := continuous_row_postcompose.measurable.comp (hrow.prodMk hD)
  change Measurable (fun w =>
    (rowFunctional (row w)).compContinuousMultilinearMap
      (iteratedFDeriv ℝ k (incrementFinVector _ C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m)
        (dyadicIncrementRawMean θ j w.1))) at hscalar
  have heq : (fun w =>
      (rowFunctional (row w)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (incrementFinVector _ C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m)
          (dyadicIncrementRawMean θ j w.1))) =
      (fun w => iteratedFDeriv ℝ k (incrementFinScalar
        C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m (row w))
        (dyadicIncrementRawMean θ j w.1)) := by
    funext w
    ext v
    exact (incrementFinScalar_iteratedFDeriv ..).symm
  rw [heq] at hscalar
  exact continuous_multilinear_pullback.measurable.comp
    (hscalar.prodMk ((incrementPilotCoordinate_measurable j).comp measurable_fst))

include hy in
/-- A finite level has a genuine bounded coefficient field on every
bounded-row, cube-supported parameter measure. This cap is used only to
justify Bochner integration; the sharper raw-energy estimate is separate. -/
theorem dyadicIncrementKernel_field_norm_bound {R : ℝ} (hR : 0 ≤ R)
    (hcube : ∀ᵐ w ∂M, w.1 ∈ unitCube d)
    (hrow : ∀ᵐ w ∂M, (∑ i, |row w i|) ≤ R) :
    ∃ B : ℝ, 0 < B ∧ ∀ᵐ w ∂M, ‖dyadicIncrementKernel θ j w.1 y m (row w) k‖ ≤ B := by
  obtain ⟨D, A, hD, hA, hder⟩ := uniform_domain_admissible_dyadic_increment_all_derivative_bound C C.holderBound_pos.le
  obtain ⟨L, hL, hmap⟩ := incrementPilotCoordinate_uniform_bound j
  refine ⟨max 1 (R * D * k.factorial * A ^ k * L ^ k), zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  filter_upwards [hcube, hrow] with w hw hr
  apply le_trans _ (le_max_right _ _)
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  exact mul_le_mul (by
    apply (hder C.originalDomain θ hθ j w.1 hw y hy m k (row w)).trans
    gcongr) ((Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hmap _ hw)).trans_eq (by simp)) (by positivity) (by positivity)

include hy hrowMeas in
theorem dyadicIncrementKernel_weighted_integrable [IsFiniteMeasure M]
    {R : ℝ} (hR : 0 ≤ R) (hcube : ∀ᵐ w ∂M, w.1 ∈ unitCube d)
    (hrow : ∀ᵐ w ∂M, (∑ i, |row w i|) ≤ R) {ν : Covariate d × Covariate d → ℝ}
    (hν : MemLp ν 2 M) :
    Integrable (fun w => ν w • dyadicIncrementKernel θ j w.1 y m (row w) k) M := by
  obtain ⟨B, _, hcap⟩ := dyadicIncrementKernel_field_norm_bound hθ j hy m k hR hcube hrow
  exact (hν.integrable (by norm_num)).smul_bdd B
    (dyadicIncrementKernel_field_measurable hθ j y m k hrowMeas).aestronglyMeasurable hcap

end NearlyMinimax
