module

public import PottsDiscontinuity.TorusExploration.MultiSeedClusterExploration

/-! The exact finite record of complete cluster explorations and the events
of distinct prescribed connections determined by it. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open FK
variable {V : Type*} [Finite V] (G : SimpleGraph V)
noncomputable section
open scoped Classical
local instance clusterRecordEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- The revealed edge set together with all its recorded open edges. -/
def clusterRecord (S : Finset V) (A : Configuration G) : Configuration G × Configuration G :=
  (actualMultiClusterReveal G S A,A ∩ actualMultiClusterReveal G S A)

section
variable (S : Finset V) (A B : Configuration G)
theorem clusterRecord_eq_iff  :
    clusterRecord G S B=clusterRecord G S A ↔
      B ∈ revealRecordEvent G (actualMultiClusterReveal G S) A := by
  simp_all [clusterRecord, revealRecordEvent]

theorem seed_connection_iff_of_record (h : clusterRecord G S B=clusterRecord G S A) {s : V} (hs : s ∈ S) (v : V) :
    ActualConnected G B s v ↔ ActualConnected G A s v := by
  have hsub := actualClusterReveal_subset_multi S A hs
  have hag : B ∩ actualClusterReveal G s A = A ∩ actualClusterReveal G s A := by
    ext e
    have he := Finset.ext_iff.1 (((clusterRecord_eq_iff G S A B).1 h).2) e
    grind
  exact actualConnected_iff_of_reveal_agreement G s A B hag v
end

/-- The first j seeds connect to their targets in pairwise distinct actual
open clusters. The endpoints themselves are fixed original graph vertices. -/
def distinctConnections (x y : ℕ → V) (j : ℕ) : Set (Configuration G) :=
  {A | (∀ i, i < j → ActualConnected G A (x i) (y i)) ∧
    ∀ i, i < j → ∀ k, k < j → i ≠ k → ¬ ActualConnected G A (x i) (x k)}

/-- Seeds exposed before the next exploration step. -/
def prefixSeeds (x : ℕ → V) (j : ℕ) : Finset V := (Finset.range j).image x

theorem distinctConnections_record_measurable (x y : ℕ → V) (j : ℕ)
    (A B : Configuration G)
    (h : clusterRecord G (prefixSeeds x j) B=clusterRecord G (prefixSeeds x j) A) :
    B ∈ distinctConnections G x y j ↔ A ∈ distinctConnections G x y j := by
  have hc (i : ℕ) (hi : i < j) (v : V) :=
    seed_connection_iff_of_record G _ A B h (Finset.mem_image.2 ⟨i,Finset.mem_range.2 hi,rfl⟩) v
  constructor
  · rintro ⟨h₁,h₂⟩
    exact ⟨fun i hi => (hc i hi _).1 (h₁ i hi),
      fun i hi k hk hik hh => h₂ i hi k hk hik ((hc i hi _).2 hh)⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨fun i hi => (hc i hi _).2 (h₁ i hi),
      fun i hi k hk hik hh => h₂ i hi k hk hik ((hc i hi _).1 hh)⟩

end
end PottsDiscontinuity.TorusExploration
