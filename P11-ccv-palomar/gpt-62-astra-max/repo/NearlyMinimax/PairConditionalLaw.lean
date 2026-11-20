module

public import NearlyMinimax.ConditionalLaw
public import NearlyMinimax.ObservationMoments


@[expose] public section

/-! Two-observation Bochner disintegration on the actual observation law. -/
noncomputable section
open MeasureTheory
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

theorem observationPair_integral_conditioning {d : ℕ} {C : ModelConstants d}
    {θ : RegressionParameter d} (hθ : Admissible C θ)
    {g : Observation d × Observation d → ℝ}
    (hg : Integrable g ((observationLaw θ).prod (observationLaw θ))) :
    (∫ z, g z ∂(observationLaw θ).prod (observationLaw θ)) =
      ∫ x,
        ∫ u, g ((x.1, θ.regression x.1 + u.1),
          (x.2, θ.regression x.2 + u.2)) ∂(θ.errors x.1).prod (θ.errors x.2)
        ∂(designLaw θ).prod (designLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  let := designLaw_isProbability C θ hθ
  have ho := measurePreserving_finTwoArrow (observationLaw θ)
  have hd := measurePreserving_finTwoArrow (designLaw θ)
  have he : ∀ x : DesignSample d 2,
      (∫ u, g ((x 0, θ.regression (x 0) + u 0), (x 1, θ.regression (x 1) + u 1))
        ∂conditionalErrorLaw θ x) =
      ∫ u, g ((x 0, θ.regression (x 0) + u.1),
        (x 1, θ.regression (x 1) + u.2)) ∂(θ.errors (x 0)).prod (θ.errors (x 1)) := fun x => (measurePreserving_piFinTwo (fun i => θ.errors (x i))).integral_comp' (fun u => g ((x 0, θ.regression (x 0) + u.1), (x 1, θ.regression (x 1) + u.2)))
  calc
    _ = _ :=
      (ho.integral_comp' g).symm
    _ = ∫ x : DesignSample d 2,
        ∫ u, g ((x 0, θ.regression (x 0) + u 0), (x 1, θ.regression (x 1) + u 1))
          ∂conditionalErrorLaw θ x ∂designVectorLaw θ 2 := sampleLaw_integral_conditioning hθ (ho.integrable_comp_of_integrable hg)
    _ = ∫ x,
        ∫ u, g ((x 0, θ.regression (x 0) + u.1),
          (x 1, θ.regression (x 1) + u.2)) ∂(θ.errors (x 0)).prod (θ.errors (x 1))
        ∂designVectorLaw θ 2 := by simp_rw [he]
    _ = _ := hd.integral_comp' (fun x =>
      ∫ u, g ((x.1, θ.regression x.1 + u.1),
        (x.2, θ.regression x.2 + u.2)) ∂(θ.errors x.1).prod (θ.errors x.2))

end NearlyMinimax
