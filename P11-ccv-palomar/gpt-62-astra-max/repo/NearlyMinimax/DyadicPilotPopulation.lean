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

section
variable {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ) (x : Covariate d)

def dyadicResponseMoment : AnchoredIndex d ℓ → ℝ :=
  fun γ => dyadicPilotScale d j * ∫ z in dyadicPilotCell j x,
    dyadicAnchoredFeature j x z γ * θ.regression z ∂designLaw θ

def dyadicConstantMoment : AnchoredIndex d ℓ → ℝ :=
  fun γ => dyadicPilotScale d j * ∫ z in dyadicPilotCell j x,
    dyadicAnchoredFeature j x z γ ∂designLaw θ

end

variable {d ℓ : ℕ} {C : ModelConstants d} {θ : RegressionParameter d} (hθ : Admissible C θ) (j : ℕ)
include hθ

/-- A measurable function of the observed design integrates under the exact
design marginal. This follows from the actual observation measure's map. -/
theorem observationLaw_integral_design {g : Covariate d → ℝ}
    (hg : Measurable g) : (∫ z, g z.1 ∂observationLaw θ) = ∫ x, g x ∂designLaw θ := by
  have hp := observationLaw_fst_measurePreserving hθ
  rw [← hp.map_eq]
  exact (integral_map hp.aemeasurable hg.aestronglyMeasurable).symm

theorem dyadicPilotPopulation_gram (x : Covariate d)
    (γ δ : AnchoredIndex d ℓ) :
    dyadicPilotPopulation θ j x (Sum.inl (γ, δ)) = dyadicPopulationGram θ j x γ δ := by
  unfold dyadicPilotPopulation dyadicPilotFeature
  rw [integral_const_mul]
  change dyadicPilotScale d j * (∫ z, (dyadicPilotCell j x).indicator
      (fun z => dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ) z.1
        ∂observationLaw θ) = dyadicPilotScale d j * _
  have hg : Measurable (fun z => dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ) :=
    (dyadicAnchoredFeature_measurable j x γ).mul (dyadicAnchoredFeature_measurable j x δ)
  rw [observationLaw_integral_design hθ
    (hg.indicator (dyadicPilotCell_measurable j x)), integral_indicator (dyadicPilotCell_measurable j x)]

theorem dyadicPilotPopulation_constant (x : Covariate d)
    (γ : AnchoredIndex d ℓ) :
    dyadicPilotPopulation θ j x (Sum.inr (Sum.inr γ)) = dyadicConstantMoment θ j x γ := by
  unfold dyadicPilotPopulation dyadicPilotFeature
  rw [integral_const_mul]
  change dyadicPilotScale d j * (∫ z, (dyadicPilotCell j x).indicator
      (fun z => dyadicAnchoredFeature j x z γ) z.1 ∂observationLaw θ) = _
  rw [observationLaw_integral_design hθ
    ((dyadicAnchoredFeature_measurable j x γ).indicator (dyadicPilotCell_measurable j x)),
    integral_indicator (dyadicPilotCell_measurable j x)]
  rfl

/-- The response vector's genuine mean uses the conditional zero mean of the
original errors, even when their conditional laws depend on the design. -/
theorem dyadicPilotPopulation_response {x : Covariate d}
    (hx : x ∈ unitCube d) (γ : AnchoredIndex d ℓ) :
    dyadicPilotPopulation θ j x (Sum.inr (Sum.inl γ)) = dyadicResponseMoment θ j x γ := by
  let := observationLaw_isProbability C θ hθ
  unfold dyadicPilotPopulation
  rw [observationLaw_integral_conditioning hθ
    ((dyadicPilotFeature_memLp_two hθ j hx (Sum.inr (Sum.inl γ))).integrable (by norm_num))]
  have heq : (fun z => ∫ u, dyadicPilotFeature j x (Sum.inr (Sum.inl γ))
      (z, θ.regression z + u) ∂θ.errors z) =ᵐ[designLaw θ]
      (fun z => dyadicPilotScale d j * (dyadicPilotCell j x).indicator
        (fun z => dyadicAnchoredFeature j x z γ * θ.regression z) z) := by
    filter_upwards [hθ.2.2.2.2.2.2.2] with z hz
    by_cases hcell : z ∈ dyadicPilotCell j x
    · have hm : Integrable (fun u : ℝ => u) (θ.errors z) := hz.1
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

theorem dyadicResponseMoment_eq_normalized (x : Covariate d) :
    dyadicResponseMoment (ℓ := ℓ) θ j x =
      anchoredVectorMoment (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x)
        (θ.regression ∘ dyadicCellAffine j x) := by
  ext γ
  simp only [dyadicResponseMoment, dyadic_design_integral hθ, dyadicCellAffine, dyadicAnchoredFeature_affine,
    anchoredVectorMoment, Function.comp_apply, mul_assoc]
  rfl

theorem dyadicConstantMoment_eq_normalized (x : Covariate d) :
    dyadicConstantMoment (ℓ := ℓ) θ j x =
      anchoredVectorMoment (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x) (fun _ => 1) := by
  ext γ
  simp only [dyadicConstantMoment, dyadic_design_integral hθ, dyadicCellAffine, dyadicAnchoredFeature_affine,
    anchoredVectorMoment, mul_one]
  rfl

end NearlyMinimax
