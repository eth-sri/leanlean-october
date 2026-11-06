module

public import NearlyMinimax.DyadicPilotMultilevel
public import NearlyMinimax.PilotModelEnvelope

@[expose] public section

/-! One genuine model envelope and one factorial series simultaneously
control both scalar coefficient families of the actual estimator. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
variable {d : ℕ} (C : ModelConstants d) [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ) (n J L : ℕ) (hJL : J ≤ L) (y : ℝ) (hy : |y| ≤ max C.holderBound 1) (m : ℕ → ℕ) (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n) (ν : Covariate d × Covariate d → ℝ) (hν : MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (pow_pos Nat.zero_lt_two L)))
include hθ hJL hy hdegree hν

theorem dyadicMultilevelErrorField_envelope_test_moment_facts  :
    MemLp (fun t => ∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w
      ∂regularPairDesignMeasure θ (2 ^ L) (by positivity)) 2 (sampleLaw θ n) ∧
    (∫ t, ∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w
      ∂regularPairDesignMeasure θ (2 ^ L) (by positivity) ∂sampleLaw θ n) = 0 := by
  letI : Nonempty (AnchoredIndex d (pilotModelConstants C).order) :=
    inferInstanceAs (Nonempty (AnchoredIndex d C.order))
  exact dyadicMultilevelErrorField_test_moment_facts (pilotModelConstants C) θ
    (admissible_pilotModelConstants C θ hθ) n J L hJL y hy m hdegree ν hν

theorem dyadicMultilevelErrorField_envelope_weighted_integrable 
    t :
    Integrable (fun w => ν w * dyadicMultilevelErrorField C θ n J y m t w)
      (regularPairDesignMeasure θ (2 ^ L) (by positivity)) := by
  letI : Nonempty (AnchoredIndex d (pilotModelConstants C).order) :=
    inferInstanceAs (Nonempty (AnchoredIndex d C.order))
  have hi (j : Fin (J + 1)) := dyadicPilotErrorField_weighted_integrable (pilotModelConstants C) θ
    (admissible_pilotModelConstants C θ hθ) n j.val L ((Nat.le_of_lt_succ j.isLt).trans hJL)
      y hy (m j.val) (hdegree j) ν hν t
  have hsum := integrable_finsetSum Finset.univ (fun j _ => hi j)
  convert hsum using 1
  funext w
  simp only [dyadicMultilevelErrorField, Finset.mul_sum]
  rfl
end


end NearlyMinimax
