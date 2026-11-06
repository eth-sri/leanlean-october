module

public import PottsDiscontinuity.Duality.ScreenBridge
public import PottsDiscontinuity.Potts.BoxObservation
public import PottsDiscontinuity.Potts.LocalWiredConnections

/-! Increasing clopen events encoding finite wired connection data. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section


section
variable (ω : FK.LatticeConfiguration)
/-- The frozen infinite open graph retains exactly the sampled lattice bonds. -/
theorem infiniteOpenGraph_adj_iff (x y : ℤ × ℤ) :
    (rcInfiniteOpenGraph ω).Adj x y ↔
      ∃ h : squareLattice.Adj x y, ω ⟨s(x, y), squareLattice.mem_edgeSet.mpr h⟩ = true := by
  rw [rcInfiniteOpenGraph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · simp_all
  grind

theorem infiniteOpenGraph_le  : rcInfiniteOpenGraph ω ≤ squareLattice := by
  intro x y hxy
  grind [infiniteOpenGraph_adj_iff]
end

section
variable (n : ℕ)
/-- Wire the boundary of a sampled finite edge configuration to the ghost. -/
def wiredObservationGraph (C : FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))) :
    SimpleGraph (Option ↥(box n : Set (ℤ × ℤ))) :=
  { Adj := fun a b => match a, b with
      | none, none => False
      | some x, some y => (FK.openGraph _ C).Adj x y
      | some x, none => x.val ∈ vertexBoundary (box n)
      | none, some y => y.val ∈ vertexBoundary (box n)
    symm := by
      constructor
      intro a b h
      cases a <;> cases b
      · omega
      · omega
      · omega
      · exact h.symm
    loopless := by
      constructor
      grind }

theorem wiredObservationGraph_eq (ω : FK.LatticeConfiguration) :
    wiredObservationGraph n (boxObservation n ω) = finiteWiredConnectionGraph (rcInfiniteOpenGraph ω) n := by
  ext a b
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some y => rfl
  | some x =>
    cases b with
    | none => rfl
    | some y =>
      change (FK.openGraph _ (boxObservation n ω)).Adj x y ↔ (rcInfiniteOpenGraph ω).Adj x.val y.val
      unfold boxObservation
      rw [openGraph_bool_adj_iff, infiniteOpenGraph_adj_iff]
      rfl
end

section
variable (n : ℕ) (F : Finset (Option (ℤ × ℤ) × Option (ℤ × ℤ)))
/-- The finite FK event asserting the indicated connections, including marks. -/
def wiredDataFiniteEvent  :
    Set (FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))) :=
  {C | ∀ z ∈ F, (wiredObservationGraph n C).Reachable
    (boxGhostProjection n z.1) (boxGhostProjection n z.2)}

/-- Positive moments of the finite wired connection partition. -/
def wiredDataEvent  :
    Set FK.LatticeConfiguration :=
  {ω | ∀ z ∈ F, localWiredSetoid (rcInfiniteOpenGraph ω) n z.1 z.2}
end

/-- Positive moments of the partition with every infinite cluster merged. -/
def infiniteMergedDataEvent (F : Finset (Option (ℤ × ℤ) × Option (ℤ × ℤ))) :
    Set FK.LatticeConfiguration :=
  {ω | ∀ z ∈ F, infiniteMergedSetoid (rcInfiniteOpenGraph ω) z.1 z.2}

section
variable (n : ℕ) (F : Finset (Option (ℤ × ℤ) × Option (ℤ × ℤ)))
theorem wiredDataEvent_eq_observation  :
    wiredDataEvent n F = boxObservationEvent n (wiredDataFiniteEvent n F) := by
  ext ω
  change (∀ z ∈ F, localWiredSetoid (rcInfiniteOpenGraph ω) n z.1 z.2) ↔
    ∀ z ∈ F, (wiredObservationGraph n (boxObservation n ω)).Reachable
      (boxGhostProjection n z.1) (boxGhostProjection n z.2)
  rw [wiredObservationGraph_eq]
  rfl

theorem wiredDataEvent_isClopen  : IsClopen (wiredDataEvent n F) := by
  rw [wiredDataEvent_eq_observation]
  exact boxObservationEvent_isClopen _ _
end

section
variable (F : Finset (Option (ℤ × ℤ) × Option (ℤ × ℤ)))
theorem wiredDataEvent_antitone  :
    Antitone (fun n => wiredDataEvent n F) := by
  intro m n hmn ω hω z hz
  exact localWiredSetoid_antitone _ (infiniteOpenGraph_le ω) hmn (hω z hz)

theorem iInter_wiredDataEvent  :
    (⋂ n, wiredDataEvent n F) = infiniteMergedDataEvent F := by
  ext ω
  simp
  constructor
  · intro h z hz
    exact (localWiredSetoid_limit _ (infiniteOpenGraph_le ω) _ _).mp (fun n => h n z hz)
  · intro h n z hz
    exact (localWiredSetoid_limit _ (infiniteOpenGraph_le ω) _ _).mpr (h z hz) n
end

theorem wiredDataFiniteEvent_upper (n : ℕ)
    (F : Finset (Option (ℤ × ℤ) × Option (ℤ × ℤ))) : IsUpperSet (wiredDataFiniteEvent n F) := by
  intro C D hCD hC z hz
  have hg : wiredObservationGraph n C ≤ wiredObservationGraph n D := by
    intro a b hab
    cases a <;> cases b
    · simp_all
    · tauto
    · tauto
    · change (FK.openGraph _ C).Adj _ _ at hab
      change (FK.openGraph _ D).Adj _ _
      rw [FK.openGraph_adj] at hab ⊢
      obtain ⟨e, he, heq⟩ := hab
      exact ⟨e, hCD he, heq⟩
  exact (hC z hz).mono hg

end
end PottsDiscontinuity.Potts
