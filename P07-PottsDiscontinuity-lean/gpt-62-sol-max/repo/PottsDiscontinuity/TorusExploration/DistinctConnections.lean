module

public import PottsDiscontinuity.TorusExploration.ClusterRecords

/-! The successor event in a distinct-cluster exploration. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open FK
variable {V : Type*} [Finite V] (G : SimpleGraph V)
noncomputable section
open scoped Classical

/-- The next prescribed connection is outside every previously explored seed cluster. -/
def nextDistinctConnection (x y : ℕ → V) (j : ℕ) : Set (Configuration G) :=
  {A | ActualConnected G A (x j) (y j) ∧
    ∀ i, i < j → ¬ ActualConnected G A (x i) (x j)}

omit [Finite V] in
lemma distinctConnections_succ (x y : ℕ → V) (j : ℕ) :
    distinctConnections G x y (j+1) =
      distinctConnections G x y j ∩ nextDistinctConnection G x y j := by
  ext A
  constructor
  · rintro ⟨hc,hd⟩
    exact ⟨⟨fun i hi => hc i (by omega),fun i hi k hk hik => hd i (by omega) k (by omega) hik⟩,
      hc j (by omega),fun i hi => hd i (by omega) j (by omega) (by omega)⟩
  · rintro ⟨⟨hc,hd⟩,hn,hdis⟩
    constructor
    · intro i hi
      grind
    · intro i hi k hk hik
      by_cases hij : i=j
      · subst i
        intro h
        exact hdis k (by omega) h.symm
      grind

end
end PottsDiscontinuity.TorusExploration
