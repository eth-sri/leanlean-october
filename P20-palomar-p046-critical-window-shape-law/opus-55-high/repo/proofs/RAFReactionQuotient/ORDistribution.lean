module

public import proofs.RAFReactionQuotient.ORLaw

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold

variable {R J : Type*} [Fintype R]

variable (π : R → J) (p : I) (j : J)

noncomputable def fibreParameter  : I :=
  σ $ (σ p) ^ (Finset.univ.filter $ fun r => π r = j).card

theorem fieldOR_marginal  :
    (RAFEmergenceApprox.Generic.colLaw R p).map (fieldOR π · j) =
      ambientCoordLaw (fibreParameter π p j) := by
  refine RAFEmergenceApprox.Generic.probability_prop_eq_of_false _ _ (measurable_of_finite _) ?_
  simp [fieldOR_closed_probability, ambientCoordLaw, fibreParameter]
  rfl


/-- The complete quotient ensemble is a product law with its actual fibre
probabilities. Singleton and double fibres need not have the same parameter. -/
theorem fieldOR_map [Fintype J] (π : R → J) (p : I) :
    (RAFEmergenceApprox.Generic.colLaw R p).map (fieldOR π) =
      Measure.pi (ambientCoordLaw $ fibreParameter π p ·) := by
  have he := (fieldOR_independent π p).map_fun_eq_pi_map
    (fun _ => (measurable_of_finite _).aemeasurable)
  rw [he]
  congr 1
  funext j
  exact fieldOR_marginal π p j

end RAFReactionQuotient
