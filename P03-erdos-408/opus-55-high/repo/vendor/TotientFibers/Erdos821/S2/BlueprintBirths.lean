module

public import Erdos821.Blueprint.Graph
public import Erdos821.S2.RankCount

/-! Exact P3 blueprint exports for the equality-rank combinatorics. -/

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Erdos821.Blueprint.Graph

theorem distinct_birth_expansion_proof : Erdos821.Blueprint.Graph.distinct_birth_expansion_statement := by
  intro a performed value
  let U : Finset (Finset (Finset (Fin a))) := Finset.univ.powerset.powerset
  have hfilter : U.filter Erdos821.S2.BirthCollection = U.filter BirthCollection := by
    ext π
    simp only [Finset.mem_filter, BirthCollection, Erdos821.S2.BirthCollection]
  calc
    _ = ∑ π ∈ U.filter Erdos821.S2.BirthCollection,
        if Erdos821.S2.birthEvent performed value π then Erdos821.S2.birthMobius π else 0 :=
      Erdos821.S2.distinct_birth_expansion a performed value
    _ = _ := by
      apply Finset.sum_congr hfilter
      intro π _
      have he : Erdos821.S2.birthEvent performed value π ↔ birthEvent performed value π := Iff.rfl
      by_cases hp : birthEvent performed value π
      · simp only [ite_eq_left hp, ite_eq_left (he.mpr hp), birthMobius, Erdos821.S2.birthMobius]
      simp_all

end Erdos821.Blueprint.Graph
