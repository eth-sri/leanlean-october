module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

@[expose] public section

namespace Path

variable {X : Type*} [TopologicalSpace X] {A : Set X}

/-- Regard a path whose image is contained in a subset as a path in that subset. -/
def inSubset {a b : A} (p : Path a.val b.val) (hp : Set.range p ⊆ A) : Path a b where
  toFun t := ⟨p t, hp ⟨t, rfl⟩⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

theorem homotopic_of_range_subset (hA : IsSimplyConnected A) {a b : X} (p q : Path a b)
    (hp : Set.range p ⊆ A) (hq : Set.range q ⊆ A) : p.Homotopic q := by
  letI : SimplyConnectedSpace A := hA
  exact (SimplyConnectedSpace.paths_homotopic
    (p.inSubset (a := ⟨a, hp p.source_mem_range⟩) (b := ⟨b, hp p.target_mem_range⟩) hp)
    (q.inSubset hq)).map ⟨Subtype.val, continuous_subtype_val⟩

end Path
