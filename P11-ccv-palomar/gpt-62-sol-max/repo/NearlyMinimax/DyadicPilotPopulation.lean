module

public import NearlyMinimax.DyadicGram
public import NearlyMinimax.AnchoredMoments
public import NearlyMinimax.PilotCoordinateExpansion


@[expose] public section

/-! Exact original-observation population means of the concrete raw pilot.
The conditional error centering and affine cell map are proved explicitly. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def dyadicResponseMoment {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : AnchoredIndex d ℓ → ℝ :=
  fun γ => dyadicPilotScale d j * ∫ z in dyadicPilotCell j x,
    dyadicAnchoredFeature j x z γ * θ.regression z ∂designLaw θ

def dyadicConstantMoment {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : AnchoredIndex d ℓ → ℝ :=
  fun γ => dyadicPilotScale d j * ∫ z in dyadicPilotCell j x,
    dyadicAnchoredFeature j x z γ ∂designLaw θ

section
variable {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
include hθ

theorem dyadicPilotPopulation_gram
    (γ δ : AnchoredIndex d ℓ) :
    dyadicPilotPopulation θ j x (Sum.inl (γ, δ)) = dyadicPopulationGram θ j x γ δ := by
  unfold dyadicPilotPopulation dyadicPilotFeature
  rw [integral_const_mul]
  change dyadicPilotScale d j * (∫ z, (dyadicPilotCell j x).indicator
      (fun z => dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ) z.1
        ∂observationLaw θ) = dyadicPilotScale d j * ∫ z in dyadicPilotCell j x,
          dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ ∂designLaw θ
  have hg : Measurable (fun z => dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ) :=
    (dyadicAnchoredFeature_measurable j x γ).mul (dyadicAnchoredFeature_measurable j x δ)
  rw [observationLaw_integral_design C θ hθ _
    (hg.indicator (dyadicPilotCell_measurable j x)), integral_indicator (dyadicPilotCell_measurable j x)]

theorem dyadicPilotPopulation_constant
    (γ : AnchoredIndex d ℓ) :
    dyadicPilotPopulation θ j x (Sum.inr (Sum.inr γ)) = dyadicConstantMoment θ j x γ := by
  unfold dyadicPilotPopulation dyadicPilotFeature
  rw [integral_const_mul]
  change dyadicPilotScale d j * (∫ z, (dyadicPilotCell j x).indicator
      (fun z => dyadicAnchoredFeature j x z γ) z.1 ∂observationLaw θ) = _
  rw [observationLaw_integral_design C θ hθ _
    ((dyadicAnchoredFeature_measurable j x γ).indicator (dyadicPilotCell_measurable j x)),
    integral_indicator (dyadicPilotCell_measurable j x)]
  rfl

/-- The response vector's genuine mean uses the conditional zero mean of the
original errors, even when their conditional laws depend on the design. -/
theorem dyadicPilotPopulation_response
    (hx : x ∈ unitCube d) (γ : AnchoredIndex d ℓ) :
    dyadicPilotPopulation θ j x (Sum.inr (Sum.inl γ)) = dyadicResponseMoment θ j x γ := by
  let := observationLaw_isProbability C θ hθ
  unfold dyadicPilotPopulation
  rw [observationLaw_integral_conditioning C θ hθ _
    ((dyadicPilotFeature_memLp_two C θ hθ j x hx (Sum.inr (Sum.inl γ))).integrable (by norm_num))]
  have heq : (fun z => ∫ u, dyadicPilotFeature j x (Sum.inr (Sum.inl γ))
      (z, θ.regression z + u) ∂θ.errors z) =ᵐ[designLaw θ]
      (fun z => dyadicPilotScale d j * (dyadicPilotCell j x).indicator
        (fun z => dyadicAnchoredFeature j x z γ * θ.regression z) z) := by
    filter_upwards [hθ.2.2.2.2.2.2.2] with z hz
    by_cases hcell : z ∈ dyadicPilotCell j x
    · have hm := hz.1
      have hi : (fun u => dyadicPilotFeature j x (Sum.inr (Sum.inl γ)) (z, θ.regression z + u)) =
          (fun u => dyadicPilotScale d j * ((θ.regression z + u) * dyadicAnchoredFeature j x z γ)) := by
        funext u
        simp [dyadicPilotFeature, dyadicPilotScalar, hcell]
      rw [hi, integral_const_mul, integral_mul_const]
      simp only [indicator_of_mem hcell]
      rw [integral_add (integrable_const _) hm, integral_const, hz.2.2.2.1]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul, add_zero]
      ring
    · simp [dyadicPilotFeature, hcell]
  rw [integral_congr_ae heq, integral_const_mul, integral_indicator (dyadicPilotCell_measurable j x)]
  rfl

private theorem dyadicWeightedMoment_eq_normalized
    (f : Covariate d → ℝ) (γ : AnchoredIndex d ℓ) :
    dyadicPilotScale d j * (∫ z in dyadicPilotCell j x,
      dyadicAnchoredFeature j x z γ * f z ∂designLaw θ) =
      anchoredVectorMoment (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x)
        (f ∘ dyadicCellAffine j x) γ := by
  rw [admissible_designLaw_setIntegral C θ hθ _ (dyadicPilotCell_measurable j x)]
  have h := regular_grid_cell_integral ((2 : ℕ) ^ j) (by positivity)
    (regularGridCell _ (by positivity) x)
    (fun z => θ.density z * (dyadicAnchoredFeature j x z γ * f z))
  rw [show dyadicPilotScale d j = ((((2 : ℕ) ^ j : ℕ) : ℝ)) ^ d by simp [dyadicPilotScale]]
  change _ * (∫ z in dyadicPilotCell j x, θ.density z *
    (dyadicAnchoredFeature j x z γ * f z) ∂cubeVolume d) = _ at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [] with w
  simp [dyadicNormalizedDensity, dyadicCellAffine, dyadicNormalizedAnchor,
    dyadicAnchoredFeature_affine, mul_assoc, mul_left_comm, mul_comm]

theorem dyadicResponseMoment_eq_normalized :
    dyadicResponseMoment (ℓ := ℓ) θ j x =
      anchoredVectorMoment (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x)
        (θ.regression ∘ dyadicCellAffine j x) :=
  funext (dyadicWeightedMoment_eq_normalized C θ hθ j x θ.regression)

theorem dyadicConstantMoment_eq_normalized :
    dyadicConstantMoment (ℓ := ℓ) θ j x =
      anchoredVectorMoment (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x) (fun _ => 1) := by
  funext γ
  simpa [dyadicConstantMoment, Function.comp_def] using dyadicWeightedMoment_eq_normalized C θ hθ j x (fun _ => 1) γ

end

end NearlyMinimax
