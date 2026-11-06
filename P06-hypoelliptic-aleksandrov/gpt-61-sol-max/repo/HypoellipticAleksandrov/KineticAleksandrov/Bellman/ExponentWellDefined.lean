module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HighDegreeExclusion
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureStationary
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! # The unique real supremum of genuine Bellman adjoint degrees -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Proof of the existence and uniqueness of the real least upper bound. -/
theorem existsUnique_bellmanAdjointExponent_aux (ratio : ℝ) (hRatio : 1 ≤ ratio) :
    ∃! β : ℝ, IsLUB (bellmanAdmissibleDegrees ratio) β := by


  have hsup := isLUB_csSup (⟨2, two_mem_bellmanAdmissibleDegrees ratio hRatio⟩) (⟨3, fun β hβ => (admissible_degree_lt_three ratio hRatio β hβ).le⟩)
  exact ⟨_, hsup, fun _ h => h.unique hsup⟩

end HypoellipticAleksandrov.KineticAleksandrov
