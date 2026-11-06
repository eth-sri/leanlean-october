module
public import Mathlib.Tactic

public import Erdos821.Blueprint.Graph
public import Erdos821.S2.RankCount

/-! Exact P3 blueprint exports for the equality-rank combinatorics. -/

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.Blueprint.Graph

theorem distinct_birth_expansion_proof : Erdos821.Blueprint.Graph.distinct_birth_expansion_statement := by
  intro a performed value
  let U : Finset (Finset (Finset (Fin a))) := Finset.univ.powerset.powerset
  
  calc
    _ = ∑ π ∈ U.filter Erdos821.S2.BirthCollection,
        if Erdos821.S2.birthEvent performed value π then Erdos821.S2.birthMobius π else 0 :=
      Erdos821.S2.distinct_birth_expansion a performed value
    _ = _ := by
      rfl

end Erdos821.Blueprint.Graph
