module

public import proofs.RAFReactionQuotient.ORLaw

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold

variable {R J : Type*} [Fintype R]

noncomputable def fibreParameter (π : R → J) (p : I) (j : J) : I :=
  σ ((σ p) ^ (Finset.univ.filter (fun r => π r = j)).card)

theorem fibreParameter_value (π : R → J) (p : I) (j : J) :
    (fibreParameter π p j : ℝ) =
      1-(1-(p : ℝ))^(Finset.univ.filter (fun r => π r = j)).card := by
  simp [fibreParameter]

theorem fieldOR_map [Fintype J] (π : R → J) (p : I) :
    (RAFEmergenceApprox.Generic.colLaw R p).map (fieldOR π) =
      Measure.pi (fun j => ambientCoordLaw (fibreParameter π p j)) := by
  have he := (fieldOR_independent π p).map_fun_eq_pi_map (fun _ => (measurable_of_finite _).aemeasurable)
  refine he.trans (congrArg _ (funext fun j => probability_prop_eq_of_false _ _ ?_))
  rw [Measure.map_apply (measurable_of_finite _) (.singleton _),
    show (fun ω : R → Prop => fieldOR π ω j) ⁻¹' {False} = {ω | ¬ fieldOR π ω j} by ext; simp,
    fieldOR_closed_probability, ambientCoordLaw_false]
  simp only [fibreParameter, symm_symm, ← ENNReal.coe_pow]
  congr 1

end RAFReactionQuotient
