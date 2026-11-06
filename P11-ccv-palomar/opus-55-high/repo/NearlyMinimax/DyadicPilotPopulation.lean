module

public import NearlyMinimax.DyadicGram
public import NearlyMinimax.AnchoredMoments
public import NearlyMinimax.PilotCoordinateExpansion
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Exact original-observation population means of the concrete raw pilot.
The conditional error centering and affine cell map are proved explicitly. -/
open MeasureTheory ProbabilityTheory Set Matrix
𝚺
𝚨

𝚭
𝚩

𝗃 𝔛 ἀ j x
𝗇 𝔗 𝔛 dyadicAnchoredFeature z
𝗇 𝔄 𝔗 γ
𝗇 𝔉 𝘟
𝗇 𝔊 𝔛 dyadicPilotCell
𝗇 𝔎 𝔄 * θ.regression z
𝗇 𝔒 𝗎
𝗃 𝔚 fun γ => 𝔉 * ∫ z in 𝔊, ἀ ∂designLaw θ
def dyadicResponseMoment (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : 𝔒 → ℝ :=
  𝔚 𝔎

def dyadicConstantMoment (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : 𝔒 → ℝ :=
  𝔚 𝔄

𝗇 𝔍 𝙟
𝗃 𝔙 ἀ C θ hθ
/-- A measurable function of the observed design integrates under the exact
design marginal. This follows from the actual observation measure's map. -/
theorem observationLaw_integral_design C
    θ (hθ : 𝔍) (g : 𝙀)
    (hg : Measurable g) : 𝖴₂ := by
  have hp := 𝔙 observationLaw_fst_measurePreserving
  rw [← hp.map_eq]
  exact (integral_map hp.aemeasurable hg.aestronglyMeasurable).symm

𝗇 𝔇 𝔛 dyadicPilotCell_measurable
𝗇 𝔏 fun z => 𝔄 * 𝔗 δ
𝗇 𝔓 (𝔊).indicator
𝗃 𝔜 ἀ θ j x
𝗇 𝔔 𝔜 dyadicPilotPopulation
theorem dyadicPilotPopulation_gram C
    θ (hθ : 𝔍) j x
    (γ δ : 𝔒) :
    𝔔 𝙫₂ = 𝔜 dyadicPopulationGram γ δ := by
  unfold dyadicPilotPopulation dyadicPilotFeature
  rw [integral_const_mul]
  change 𝔉 * ∫ z, 𝔓
      𝔏 z.1
        ∂observationLaw θ = 𝔉 * ∫ z in 𝔊,
          𝔄 * 𝔗 δ ∂designLaw θ
  have hg : Measurable 𝔏 :=
    (𝔛 dyadicAnchoredFeature_measurable γ).mul $ 𝔛 dyadicAnchoredFeature_measurable δ
  rw [𝔙 observationLaw_integral_design _
    $ hg.indicator 𝔇 , integral_indicator 𝔇]

theorem dyadicPilotPopulation_constant C
    θ (hθ : 𝔍) j x
    (γ : 𝔒) :
    𝔔 (Sum.inr $ Sum.inr γ ) = 𝔜 dyadicConstantMoment γ := by
  unfold dyadicPilotPopulation dyadicPilotFeature
  rw [integral_const_mul]
  change 𝔉 * ∫ z, 𝔓
      (fun z => 𝔄) z.1 ∂observationLaw θ = _
  rw [𝔙 observationLaw_integral_design _
    $ (𝔛 dyadicAnchoredFeature_measurable γ).indicator 𝔇 ,
    integral_indicator 𝔇]
  rfl

𝗇 𝔈 Sum.inr $ Sum.inl γ
𝗇 𝔐 𝔛 dyadicPilotFeature 𝔈 (z, θ.regression z + u)
/-- The response vector's genuine mean uses the conditional zero mean of the
original errors, even when their conditional laws depend on the design. -/
theorem dyadicPilotPopulation_response C
    θ (hθ : 𝔍) j x
    (hx : 𝗌) (γ : 𝔒) :
    𝔔 𝔈 = 𝔜 dyadicResponseMoment γ := by
  let := 𝔙 observationLaw_isProbability
  unfold dyadicPilotPopulation
  rw [𝔙 observationLaw_integral_conditioning _
    $ (𝔙 dyadicPilotFeature_memLp_two j x hx 𝔈).integrable 𝖠₄ ]
  have heq : (fun z => ∫ u, 𝔐 ∂θ.errors z) =ᵐ[designLaw θ]
       fun z => 𝔉 * 𝔓
        (fun z => 𝔎) z := by
    filter_upwards [hθ.2.2.2.2.2.2.2] with z hz
    by_cases hcell : z ∈ 𝔊
    · have hi : (fun u => 𝔐) =
           fun u => 𝔉 * ((θ.regression z + u) * 𝔄) := by
        funext u
        simp [dyadicPilotFeature, dyadicPilotScalar, hcell]
      rw [hi, integral_const_mul, integral_mul_const]
      simp only [indicator_of_mem hcell]
      rw [𝖻₁ hz.1 , integral_const, hz.2.2.2.1]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one]
      ring
    · simp [dyadicPilotFeature, hcell]
  rw [integral_congr_ae heq, integral_const_mul, integral_indicator 𝔇]
  rfl

𝗇 𝔅 (𝗜 : ℕ) ^ d
𝗇 𝔑 anchoredVectorMoment 𝔛 dyadicNormalizedAnchor 𝔜 dyadicNormalizedDensity
𝗇 𝔖 𝘷
𝗃 𝔘 𝔅 * ∫ z in 𝔊, θ.density z * ἀ ∂cubeVolume d = _
𝗃 𝔞 fun z => θ.density z * ἀ
theorem dyadicResponseMoment_eq_normalized C
    θ (hθ : 𝔍) j (x : Covariate d) :
    dyadicResponseMoment (ℓ := ℓ) θ j x =
      𝔑
        (θ.regression ∘ 𝔛 dyadicCellAffine) := by
  funext γ
  unfold dyadicResponseMoment
  rw [𝔙 admissible_designLaw_setIntegral _ 𝔇]
  have h := regular_grid_cell_integral 𝔖  𝖠₃ 
    (regularGridCell _  𝖠₃  x)
    𝔞 𝔎
  change 𝔘 𝔎 at h
  rw [show 𝔉 = 𝔅 by aesop]
  rw [h]
  unfold anchoredVectorMoment dyadicNormalizedDensity dyadicCellAffine dyadicNormalizedAnchor
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w => by
    dsimp
    rw [dyadicAnchoredFeature_affine]
    ring

theorem dyadicConstantMoment_eq_normalized C
    θ (hθ : 𝔍) j (x : Covariate d) :
    dyadicConstantMoment (ℓ := ℓ) θ j x =
      𝔑 𝙃 := by
  funext γ
  unfold dyadicConstantMoment
  rw [𝔙 admissible_designLaw_setIntegral _ 𝔇]
  have h := regular_grid_cell_integral 𝔖  𝖠₃ 
    (regularGridCell _ (by positivity) x) 𝔞 𝔄
  change 𝔘 𝔄 at h
  rw [show 𝔉 = 𝔅 by aesop]
  rw [h]
  unfold anchoredVectorMoment dyadicNormalizedDensity dyadicCellAffine dyadicNormalizedAnchor
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w => by
    dsimp
    rw [dyadicAnchoredFeature_affine]
    simp
