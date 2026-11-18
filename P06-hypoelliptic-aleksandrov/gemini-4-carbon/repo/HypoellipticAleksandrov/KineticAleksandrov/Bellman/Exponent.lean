module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HighDegreeExclusion
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureStationary
import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.ExponentSetting

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Proof of the existence and uniqueness of the real least upper bound. -/
theorem existsUnique_bellmanAdjointExponent_aux (ratio : ℝ) (hRatio : 1 ≤ ratio) :
    ∃! β : ℝ, IsLUB (bellmanAdmissibleDegrees ratio) β := by
  have hn : (bellmanAdmissibleDegrees ratio).Nonempty :=
    ⟨2, two_mem_bellmanAdmissibleDegrees ratio hRatio⟩
  have hb : BddAbove (bellmanAdmissibleDegrees ratio) :=
    ⟨3, fun β hβ => (admissible_degree_lt_three ratio hRatio β hβ).le⟩
  have hsup := isLUB_csSup hn hb
  exact ⟨sSup (bellmanAdmissibleDegrees ratio), hsup, fun _ h => h.unique hsup⟩

open Set

/-- The unique real supremum of the source's admissible normalized adjoint degrees. -/
def bellmanAdjointExponent (ratio : ℝ) (hRatio : 1 ≤ ratio) : ℝ :=
  (existsUnique_bellmanAdjointExponent_aux ratio hRatio).choose

/-- Full characteristic property and uniqueness of the same chosen real exponent.
This does not assert that the supremal degree is attained by an admissible pair. -/
theorem bellmanAdjointExponent_characterization (ratio : ℝ) (hRatio : 1 ≤ ratio) :
    IsLUB (bellmanAdmissibleDegrees ratio) (bellmanAdjointExponent ratio hRatio) ∧
      ∀ β : ℝ, IsLUB (bellmanAdmissibleDegrees ratio) β →
        β = bellmanAdjointExponent ratio hRatio :=
  (existsUnique_bellmanAdjointExponent_aux ratio hRatio).choose_spec

end HypoellipticAleksandrov.KineticAleksandrov

