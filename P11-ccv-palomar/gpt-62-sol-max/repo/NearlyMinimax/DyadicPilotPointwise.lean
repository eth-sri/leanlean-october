module

public import NearlyMinimax.IncrementPilotFeatures
public import NearlyMinimax.PopulationRowDerivatives
public import NearlyMinimax.DyadicFit


@[expose] public section

/-! Actual original-law factorial pilots at a dyadic anchor.  Their population
point and derivative constants are derived from the original admissibility
conditions, rather than supplied as stochastic budget assumptions. -/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix MvPolynomial
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
variable {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ)
include hθ

theorem dyadicFinPilotMoments_eq_anchored (x : Covariate d)
    (hx : x ∈ unitCube d) :
    dyadicFinPilotMoments (ℓ := ℓ) θ j x = anchoredFinMomentFamilies
      (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x)
      (θ.regression ∘ dyadicCellAffine j x) := by
  funext t i
  apply dyadicFinPilotMoments_eq_normalized <;> assumption

end

def rowIncrementPolynomial (r : ℕ) (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (row : Fin r → ℝ) :
    MvPolynomial (Fin (Fintype.card (incrementVariables r))) ℝ :=
  ∑ i, C (row i) * incrementFinPolynomial r a b T y m i

section
variable (r : ℕ)

theorem rowIncrementPolynomial_eval (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (row : Fin r → ℝ) (z : Fin (Fintype.card (incrementVariables r)) → ℝ) :
    eval z (rowIncrementPolynomial r a b T y m row) = incrementFinScalar r a b T y m row z := by
  simp [rowIncrementPolynomial, incrementFinScalar, incrementFinVector, dotProduct]

theorem rowIncrementPolynomial_degree [NeZero r] (a b : ℝ)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ) (row : Fin r → ℝ) :
    (rowIncrementPolynomial r a b T y m row).totalDegree ≤ m + r + 1 := by
  apply totalDegree_finsetSum_le
  intro i _
  apply (totalDegree_mul _ _).trans
  simpa only [totalDegree_C, zero_add, incrementFinPolynomial] using
    (totalDegree_rename_le _ _).trans (incrementEntryPolynomial_degree r a b T y m i)

end

section
variable {d ℓ : ℕ}

theorem anchoredFinNormalizedGram_one (u : Covariate d) :
    anchoredFinNormalizedGram (ℓ := ℓ) u (fun _ => 1) = 1 := by
  have hG : anchoredDensityGram (ℓ := ℓ) u (fun _ => 1) = anchoredGram u := by
    ext γ δ
    simp [anchoredDensityGram, anchoredGram]
  unfold anchoredFinNormalizedGram
  rw [hG, Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp (anchoredGram_posDef u).isUnit)]
  simp_all

end

section
variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
  (j : ℕ) (x : Covariate d)
include hθ

theorem dyadicParentDensity_measurable :
    Measurable (dyadicParent (fun _ => 1) (fun i => dyadicNormalizedDensity θ i x) j) :=
  dyadicParent_property measurable_const (fun i => dyadicNormalizedDensity_measurable C θ hθ i x) j

theorem dyadicParentDensity_bounds :
    ∀ᵐ w ∂cubeVolume d, C.densityLower ≤ dyadicParent (fun _ => 1)
      (fun i => dyadicNormalizedDensity θ i x) j w ∧
      dyadicParent (fun _ => 1) (fun i => dyadicNormalizedDensity θ i x) j w ≤ C.densityUpper :=
  dyadicParent_property (P := fun p : Covariate d → ℝ =>
    ∀ᵐ w ∂cubeVolume d, C.densityLower ≤ p w ∧ p w ≤ C.densityUpper)
    (.of_forall fun _ => ⟨C.densityLower_lt_one.le, C.one_lt_densityUpper.le⟩)
    (fun i => dyadicNormalizedDensity_bounds C θ hθ i x) j

theorem anchoredFinNormalizedGram_dyadicParent {ℓ : ℕ} :
    anchoredFinNormalizedGram (ℓ := ℓ) (dyadicNormalizedAnchor (j - 1) x)
        (dyadicParent (fun _ => 1) (fun i => dyadicNormalizedDensity θ i x) j) =
      dyadicParent 1 (fun i => dyadicFinPilotGram θ i x) j := by
  unfold dyadicParent
  split_ifs <;> simp [anchoredFinNormalizedGram_one, dyadicFinPilotGram_eq_normalized C θ hθ]

end

theorem dyadicIncrementRawMean_eq_with_virtual_parent {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ)
    (x : Covariate d) (hx : x ∈ unitCube d) :
    dyadicIncrementRawMean (ℓ := ℓ) θ j x = fun a =>
      incrementValuation
        (anchoredFinNormalizedGram (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x))
        (anchoredFinNormalizedGram (dyadicNormalizedAnchor (j - 1) x)
          (dyadicParent (fun _ => 1) (fun i => dyadicNormalizedDensity θ i x) j))
        (dyadicFinPilotMoments θ j x) (dyadicParent 0 (fun i => dyadicFinPilotMoments θ i x) j)
        ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a) := by
  rw [dyadicIncrementRawMean_eq_population C θ hθ j x hx, dyadicIncrementPopulation,
    dyadicFinPilotGram_eq_normalized C θ hθ j x, anchoredFinNormalizedGram_dyadicParent C θ hθ]

def dyadicPolynomialPilot {d : ℕ} (C : ModelConstants d) (n j : ℕ) (x : Covariate d)
    (y : ℝ) (m : ℕ) (row : Fin (anchoredDimension d C.order) → ℝ)
    (z : ObservedSample d n) : ℝ :=
  RoughRegime.Upper.polynomialLift
    (rowIncrementPolynomial (anchoredDimension d C.order) C.densityLower C.densityUpper
      (anchoredFinTransport d C.order) y m row)
    (fun i z => dyadicIncrementRawVector j x (z i)) z

section
variable {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)]

/-- The concrete coefficient lift is L² and exactly unbiased at its genuine
population polynomial, even though the observed responses are unbounded. -/
theorem dyadicPolynomialPilot_moment_facts (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n j : ℕ) (x : Covariate d) (hx : x ∈ unitCube d) (y : ℝ) (m : ℕ)
    (row : Fin (anchoredDimension d C.order) → ℝ)
    (hdegree : m + anchoredDimension d C.order + 1 ≤ n) :
    MemLp (dyadicPolynomialPilot C n j x y m row) 2 (sampleLaw θ n) ∧
    (∫ z, dyadicPolynomialPilot C n j x y m row z ∂sampleLaw θ n) =
      incrementFinScalar (anchoredDimension d C.order) C.densityLower C.densityUpper
        (anchoredFinTransport d C.order) y m row (dyadicIncrementRawMean θ j x) := by
  let := sampleLaw_isProbability C θ hθ n
  obtain ⟨hX, hmean⟩ := dyadicIncrementRawVector_sample_facts C θ hθ j x hx
  refine ⟨LiftL2.polynomialLift_memLp_two_l2 _ _ (dyadicIncrementRawMean θ j x)
    (rowIncrementPolynomial_degree _ _ _ _ _ _ _) hdegree hX.toIndependentL2, ?_⟩
  rw [← rowIncrementPolynomial_eval]
  exact LiftL2.polynomialLift_expectation_l2 _ _ (dyadicIncrementRawMean θ j x)
    (rowIncrementPolynomial_degree _ _ _ _ _ _ _) hdegree hX hmean

end

end NearlyMinimax
