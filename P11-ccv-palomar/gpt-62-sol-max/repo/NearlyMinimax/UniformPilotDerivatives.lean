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

/-- Numerical constants can be uniform over domains while admissibility still
uses the particular extension domain. -/
abbrev UniformOnExtensions {d : ℕ} (C : ModelConstants d)
    (P : ExtensionDomain d → RegressionParameter d → Prop) : Prop :=
  ∀ U θ, Admissible (C.withDomain U) θ → P U θ

/-- All scalar-row derivatives of the inverse pilot at the actual moment centers. -/
abbrev DyadicRowDerivativeBound {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (Y D A : ℝ) : Prop :=
  ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ y : ℝ, |y| ≤ Y → ∀ m k : ℕ,
  ∀ row : Fin (anchoredDimension d C.order) → ℝ,
    ‖iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
      C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row)
      (dyadicIncrementRawMean θ j x)‖ ≤ (∑ i, |row i|) * D * (k.factorial : ℝ) * A ^ k

section
variable {d : ℕ} (C : ModelConstants d)

theorem pilotModelConstants_withDomain (U : ExtensionDomain d) :
    pilotModelConstants (C.withDomain U) = (pilotModelConstants C).withDomain U := rfl

theorem uniform_domain_admissible_dyadicFinPilotMoments_uniform_bound :
    ∃ W : ℝ, 0 < W ∧ UniformOnExtensions C fun _ θ =>
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ t : Bool,
        ‖dyadicFinPilotMoments (ℓ := C.order) θ j x t‖ ≤ W := by
  obtain ⟨W, hW, hb⟩ := anchoredFinMomentFamilies_uniform_bound (d := d) (ℓ := C.order)
    C.densityUpper C.holderBound (zero_le_one.trans C.one_lt_densityUpper.le)
  refine ⟨W, hW, ?_⟩
  intro Udom θ hθ j x hx t
  rw [dyadicFinPilotMoments_eq_anchored (C.withDomain Udom) θ hθ j x hx]
  exact hb _ (gridNormalizedAnchor_mem_cube _ (by positivity) x hx) _ _
    ((dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ j x).mono
      (fun w hw => ⟨C.densityLower_pos.le.trans hw.1, hw.2⟩))
    (fun w hw => admissible_regression_value_bound (C.withDomain Udom) θ hθ _ (dyadicCellAffine_mem_cube j x w hw)) t

section
variable [Nonempty (AnchoredIndex d C.order)] (Y : ℝ) (hY : 0 ≤ Y)
include hY

/-- A common genuine vector derivative bound at all actual population means. -/
theorem uniform_domain_dyadic_increment_vector_derivative_bound :
    ∃ D A : ℝ, 0 < D ∧ 0 < A ∧
      UniformOnExtensions C fun _ θ =>
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ y : ℝ, |y| ≤ Y → ∀ m k : ℕ,
      ∀ directions : Fin k → Fin (Fintype.card (incrementVariables (anchoredDimension d C.order))) → ℝ,
        ‖iteratedFDeriv ℝ k
          (incrementFinVector (anchoredDimension d C.order) C.densityLower C.densityUpper
            (anchoredFinTransport d C.order) y m)
          (dyadicIncrementRawMean θ j x) directions‖ ≤
          D * (k.factorial : ℝ) * A ^ k * ∏ i, ‖directions i‖ := by
  obtain ⟨W, hW, hmom⟩ := uniform_domain_admissible_dyadicFinPilotMoments_uniform_bound C
  obtain ⟨B, A, hB, hA, hder⟩ := anchored_population_inverse_derivatives
    (d := d) (ℓ := C.order) C.densityLower C.densityUpper W Y C.densityLower_pos
    (C.densityLower_lt_one.trans C.one_lt_densityUpper) hW.le hY
  refine ⟨B, A, hB, hA, ?_⟩
  intro Udom θ hθ j x hx y hy m k directions
  let q := dyadicParent (fun _ => 1) (fun i => dyadicNormalizedDensity θ i x) j
  have hV : ∀ t : Bool, ‖(dyadicParent 0 (fun i => dyadicFinPilotMoments (ℓ := C.order) θ i x) j) t‖ ≤ W :=
    dyadicParent_property (P := fun f : Bool → Fin (anchoredDimension d C.order) → ℝ => ∀ t, ‖f t‖ ≤ W)
      (by simpa using hW.le) (fun i => hmom Udom θ hθ i x hx) j
  have hd := hder (dyadicNormalizedAnchor j x) (dyadicNormalizedAnchor (j - 1) x)
    (gridNormalizedAnchor_mem_cube ((2 : ℕ) ^ j) (by positivity) x hx)
    (gridNormalizedAnchor_mem_cube ((2 : ℕ) ^ (j - 1)) (by positivity) x hx)
    (dyadicNormalizedDensity θ j x) q
    (dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ j x)
    (dyadicParentDensity_measurable (C.withDomain Udom) θ hθ j x)
    (dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ j x)
    (dyadicParentDensity_bounds (C.withDomain Udom) θ hθ j x)
    (dyadicFinPilotMoments θ j x) (dyadicParent 0 (fun i => dyadicFinPilotMoments θ i x) j)
    (hmom Udom θ hθ j x hx) hV y hy m k directions
  rw [← dyadicIncrementRawMean_eq_with_virtual_parent (C.withDomain Udom) θ hθ j x hx] at hd
  assumption

/-- Uniform-domain U5(4) after arbitrary scalar feature-row postcomposition.
The constants precede the domain and all polynomial/derivative orders. -/
theorem uniform_domain_admissible_dyadic_increment_all_derivative_bound :
    ∃ D A : ℝ, 0 < D ∧ 0 < A ∧
      UniformOnExtensions C fun _ θ =>
        DyadicRowDerivativeBound C θ Y D A := by
  obtain ⟨D, A, hD, hA, hder⟩ := uniform_domain_dyadic_increment_vector_derivative_bound C Y hY
  refine ⟨D, A, hD, hA, ?_⟩
  intro Udom θ hθ j x hx y hy m k row
  have hrow : 0 ≤ ∑ i, |row i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro directions
  rw [incrementFinScalar_iteratedFDeriv]
  calc
    _ ≤ ‖rowFunctional row‖ * ‖iteratedFDeriv ℝ k
        (incrementFinVector (anchoredDimension d C.order) C.densityLower C.densityUpper
          (anchoredFinTransport d C.order) y m)
        (dyadicIncrementRawMean θ j x) directions‖ := (rowFunctional row).le_opNorm _
    _ ≤ (∑ i, |row i|) * (D * (k.factorial : ℝ) * A ^ k * ∏ i, ‖directions i‖) :=
      mul_le_mul (rowFunctional_norm_le row) (hder Udom θ hθ j x hx y hy m k directions) (norm_nonneg _) hrow
    _ = ((∑ i, |row i|) * D * (k.factorial : ℝ) * A ^ k) * ∏ i, ‖directions i‖ := by ring

end

end

end NearlyMinimax
