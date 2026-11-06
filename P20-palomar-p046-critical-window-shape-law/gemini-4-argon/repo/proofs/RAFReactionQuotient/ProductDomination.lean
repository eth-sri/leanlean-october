module

public import proofs.RAFReactionQuotient.ORDistribution
public import proofs.HordijkSteelThreshold.StaticDecreasingEvents

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold

noncomputable def halfParameter (a : I) : I := ⟨(a : ℝ)/2, by
  constructor
  · exact div_nonneg a.2.1 (by norm_num)
  · have := a.2.2; linarith⟩

theorem fibreParameter_half_le {R J : Type*} [Fintype R]
    (π : R → J) (a : I) (j : J)
    (hm : (Finset.univ.filter (fun r => π r = j)).card ≤ 2) :
    fibreParameter π (halfParameter a) j ≤ a := by
  change (fibreParameter π (halfParameter a) j : ℝ) ≤ (a : ℝ)
  rw [fibreParameter_value]
  have ha0 := a.2.1
  have ha1 := a.2.2
  let m := (Finset.univ.filter (fun r => π r = j)).card
  change 1-(1-(a : ℝ)/2)^m ≤ (a : ℝ)
  have hm' : m ≤ 2 := hm
  interval_cases m <;> norm_num <;> nlinarith

end RAFReactionQuotient
