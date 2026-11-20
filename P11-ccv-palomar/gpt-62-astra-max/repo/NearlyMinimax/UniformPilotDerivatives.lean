module

public import NearlyMinimax.DyadicPilotPointwise
public import NearlyMinimax.PaperGoals
public import NearlyMinimax.PilotModelEnvelope


@[expose] public section

/-! Genuine all-order inverse-pilot derivative witnesses chosen before every
extension domain, including the actual identity/zero virtual parent at root. -/
noncomputable section
open Matrix MeasureTheory Set
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {d : ℕ} (C : ModelConstants d)

theorem dyadicIncrementRawMean_eq_with_virtual_parent {ℓ : ℕ} {C : ModelConstants d}
    {θ : RegressionParameter d} (hθ : Admissible C θ) (j : ℕ)
    {x : Covariate d} (hx : x ∈ unitCube d) :
    dyadicIncrementRawMean θ j x = fun a =>
      incrementValuation
        (anchoredFinNormalizedGram (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x))
        (anchoredFinNormalizedGram (dyadicNormalizedAnchor (j - 1) x)
          (if j = 0 then (fun _ => 1) else dyadicNormalizedDensity θ (j - 1) x))
        (dyadicFinPilotMoments θ j x) (if j = 0 then 0 else dyadicFinPilotMoments θ (j - 1) x)
        ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a) := by
  rw [dyadicIncrementRawMean_eq_population hθ j hx]
  unfold dyadicIncrementPopulation
  rw [dyadicFinPilotGram_eq_normalized hθ j x]
  by_cases hj : j = 0
  · simp [hj, anchoredFinNormalizedGram_one]
  · simp [hj]
    rw [dyadicFinPilotGram_eq_normalized hθ (j - 1) x]

theorem uniform_domain_admissible_dyadicFinPilotMoments_uniform_bound :
    ∃ W : ℝ, 0 < W ∧ ∀ Udom, ∀ θ, Admissible (C.withDomain Udom) θ →
      ∀ j, ∀ x ∈ unitCube d, ∀ t,
        ‖dyadicFinPilotMoments (ℓ := C.order) θ j x t‖ ≤ W := by
  obtain ⟨W, hW, hb⟩ := anchoredFinMomentFamilies_uniform_bound (zero_le_one.trans C.one_lt_densityUpper.le) C.holderBound_pos.le
  refine ⟨W, hW, ?_⟩
  intro Udom θ hθ j x hx t
  rw [((by funext t i; exact dyadicFinPilotMoments_eq_normalized hθ j hx t i : dyadicFinPilotMoments θ j x = anchoredFinMomentFamilies (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x) (θ.regression ∘ dyadicCellAffine j x)))]
  exact hb _ (gridNormalizedAnchor_mem_cube _ (by positivity) hx) _ _
    ((dyadicNormalizedDensity_bounds hθ j x).mono
      (fun w hw => ⟨C.densityLower_pos.le.trans hw.1, hw.2⟩))
    (fun w hw => admissible_regression_value_bound hθ (dyadicCellAffine_mem_cube j x w hw)) t

/-- A common genuine vector derivative bound at all actual population means. -/
theorem uniform_domain_dyadic_increment_vector_derivative_bound
    [Nonempty (AnchoredIndex d C.order)] {Y : ℝ} (hY : 0 ≤ Y) :
    ∃ D A : ℝ, 0 < D ∧ 0 < A ∧
      ∀ Udom, ∀ θ, Admissible (C.withDomain Udom) θ →
      ∀ j, ∀ x ∈ unitCube d, ∀ y, |y| ≤ Y → ∀ m k,
      ∀ directions,
        ‖iteratedFDeriv ℝ k
          (incrementFinVector (anchoredDimension d C.order) C.densityLower C.densityUpper
            (anchoredFinTransport d C.order) y m)
          (dyadicIncrementRawMean θ j x) directions‖ ≤
          D * k.factorial * A ^ k * ∏ i, ‖directions i‖ := by
  obtain ⟨W, hW, hmom⟩ := uniform_domain_admissible_dyadicFinPilotMoments_uniform_bound C
  obtain ⟨B, A, hB, hA, hder⟩ := anchored_population_inverse_derivatives
    (d := d) (ℓ := C.order) C.densityLower_pos
    (C.densityLower_lt_one.trans C.one_lt_densityUpper) hW.le hY
  refine ⟨B, A, hB, hA, ?_⟩
  intro Udom θ hθ j x hx y hy m k directions
  let q := if j = 0 then (fun _ => 1) else dyadicNormalizedDensity θ (j - 1) x
  have hqm : Measurable q := by
    by_cases hj : j = 0
    · simpa [q, hj] using measurable_const
    · simpa [q, hj] using dyadicNormalizedDensity_measurable hθ (j - 1) x
  have hqb : ∀ᵐ w ∂cubeVolume d, C.densityLower ≤ q w ∧ q w ≤ C.densityUpper := by
    by_cases hj : j = 0
    · exact Filter.Eventually.of_forall (fun _ => by
        simpa [q, hj] using And.intro C.densityLower_lt_one.le C.one_lt_densityUpper.le)
    · simpa [q, hj, ModelConstants.withDomain] using dyadicNormalizedDensity_bounds hθ (j - 1) x
  have hV t : ‖(if j = 0 then (0 : Bool → Fin (anchoredDimension d C.order) → ℝ)
      else dyadicFinPilotMoments θ (j - 1) x) t‖ ≤ W := by
    by_cases hj : j = 0
    · simpa [hj] using hW.le
    · simpa only [hj, ite_false] using hmom Udom θ hθ (j - 1) x hx t
  have hd := hder (dyadicNormalizedAnchor j x) (dyadicNormalizedAnchor (j - 1) x) (gridNormalizedAnchor_mem_cube (2 ^ j) (by positivity) hx) (gridNormalizedAnchor_mem_cube (2 ^ (j - 1)) (by positivity) hx) (dyadicNormalizedDensity θ j x) q (dyadicNormalizedDensity_measurable hθ j x) hqm (dyadicNormalizedDensity_bounds hθ j x) hqb (dyadicFinPilotMoments θ j x) _ (hmom Udom θ hθ j x hx) hV y hy m k directions
  rw [← dyadicIncrementRawMean_eq_with_virtual_parent hθ j hx] at hd
  exact hd

/-- Uniform-domain U5(4) after arbitrary scalar feature-row postcomposition.
The constants precede the domain and all polynomial/derivative orders. -/
theorem uniform_domain_admissible_dyadic_increment_all_derivative_bound
    [Nonempty (AnchoredIndex d C.order)] {Y : ℝ} (hY : 0 ≤ Y) :
    ∃ D A : ℝ, 0 < D ∧ 0 < A ∧
      ∀ Udom, ∀ θ, Admissible (C.withDomain Udom) θ →
        PilotDerivativeBound C θ Y D A := by
  obtain ⟨D, A, hD, hA, hder⟩ := uniform_domain_dyadic_increment_vector_derivative_bound C hY
  refine ⟨D, A, hD, hA, ?_⟩
  intro Udom θ hθ j x hx y hy m k row
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro directions
  rw [incrementFinScalar_iteratedFDeriv]
  calc
    _ ≤ _ := (rowFunctional row).le_opNorm _
    _ ≤ _ :=
      mul_le_mul (rowFunctional_norm_le row) (hder Udom θ hθ j x hx y hy m k directions) (norm_nonneg _) (Finset.sum_nonneg (fun i _ => abs_nonneg _))
    _ = _ := by ring

end NearlyMinimax
