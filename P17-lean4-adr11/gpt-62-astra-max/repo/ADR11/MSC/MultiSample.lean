module
public import ADR11.Trees.Metric
public import ADR11.MSC.Pullback

/-! Replace every taxon by a star on its sampled lineages. Internal edges
of this extended tree recover precisely the measurable edges of the original. -/
@[expose] public section
namespace ADR11
open Finset
variable {X L : Type*} [Fintype X] [DecidableEq X] [Fintype L] [DecidableEq L]

namespace SpeciesTree
variable (σ : SpeciesTree X) {s : L → X} (hs : Function.Surjective s)

noncomputable abbrev extend := σ.pull s (by
  obtain ⟨x,_⟩ := σ.nonempty_of_mem _ σ.univ_mem
  obtain ⟨l,rfl⟩ := hs x; exact ⟨l,mem_univ _⟩)

/-- Under a surjection a trace fibre consists of a single source subset. -/
theorem extend_edge {A : Finset X} (h2 : 2 ≤ #(pre s A)) (hu : A ≠ univ) : (σ.extend hs).edge (pre s A) = σ.edge A := by
  rw [extend,σ.pull_edge _ _ h2]; · simp [sum_filter,(pre_injective hs).eq_iff]
  exact fun e => hu (pre_injective hs (e.trans (pre_univ _).symm))

end SpeciesTree
end ADR11
