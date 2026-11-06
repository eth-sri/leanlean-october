module

public import proofs.HordijkSteelThreshold.NestedColumnHistory
public import proofs.HordijkSteelThreshold.AmbientIndependence
public import proofs.HordijkSteelThreshold.PeelingHistory
public import proofs.HordijkSteelThreshold.FiniteInitialSegments

@[expose] public section

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory
open RAF RAF.Polymer RAF.Concrete

variable {X R : Type*} [Fintype X]

def activeTrace
    (response : Finset X → Finset R) (closure : Finset R → Finset X) (T : ℕ) :
    Fin (T + 1) → R → Prop :=
  fun t r => r ∈ peelingActiveAt response closure t.val

open Classical in
noncomputable def traceHistory {R : Type*} [Fintype R] {T : ℕ}
    (H : Fin (T + 1) → R → Prop) (t : ℕ) : Finset R :=
  if ht : t < T + 1 then Finset.univ.filter (H ⟨t, ht⟩) else ∅

theorem activeTrace_eq_iff  [Fintype R]
    (response : Finset X → Finset R) (closure : Finset R → Finset X) (T : ℕ)
    (H : Fin (T + 1) → R → Prop) :
    activeTrace response closure T = H ↔
      ∀ t ≤ T, peelingActiveAt response closure t = traceHistory H t := by
  simp only [funext_iff, activeTrace, traceHistory]
  grind

end HordijkSteelThreshold
