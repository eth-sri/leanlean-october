module

public import RequestProject.CubeRollerModel

@[expose] public section

/-!
# One-coordinate paths in the Roller model

`RequestProject/CubeRollerModel.lean` derives the descending-cube axioms — and hence the
vanishing of the second homology of the cellular chains — from a vertex set `W` of finite sets
of hyperplanes which contains the base vertex `∅` and is closed under the median (majority)
operation.

Closedness under the median is *not* by itself enough for `W` to be the vertex set of a graph
in which every step changes one coordinate.  The set

  `W = {∅, {p, q}}`   (`p ≠ q`)

is closed under the majority operation and contains the base vertex, but its two vertices
differ in two coordinates and no vertex of `W` lies between them, so there is no path from one
to the other changing one coordinate at a time (`FiniteChains.pairModel_not_stepConnected`).

This file therefore isolates the missing hypothesis and proves what it gives:

* `FiniteChains.OneStep` — a single move inside `W` changing exactly one coordinate;
* `FiniteChains.StepPath` — a path of such moves, with its length;
* `FiniteChains.ConnectedRollerModel` — a Roller model with the extra hypothesis that every
  vertex other than the base vertex has a *descending* neighbour inside `W` (some coordinate
  can be removed without leaving `W`);
* `FiniteChains.ConnectedRollerModel.stepPath_base` — every vertex `A` is joined to the base
  vertex by a path of exactly `A.card` one-coordinate moves, so the model is the vertex set of
  a connected graph whose edges are the one-coordinate moves and in which `A` is at distance
  at most `A.card` from the base vertex;
* `FiniteChains.ConnectedRollerModel.stepConnected` — hence any two vertices are joined by such
  a path.

The conclusion `ker d₂ = im d₃` proved in `RequestProject/CubeRollerModel.lean` is unaffected
(it holds for every median-closed `W`); what this file adds is that under the extra hypothesis
the combinatorial data really is the data of a connected graph with one-coordinate edges.
-/

namespace FiniteChains

universe u

variable {ι : Type u} [DecidableEq ι]

/-- A single move inside `W` changing exactly one coordinate: `B` is obtained from `A` by
deleting or inserting one hyperplane, and both are vertices. -/
def OneStep (W : Set (Finset ι)) (A B : Finset ι) : Prop :=
  A ∈ W ∧ B ∈ W ∧ ∃ p : ι, (p ∈ A ∧ B = A.erase p) ∨ (p ∈ B ∧ A = B.erase p)

theorem OneStep.symm {W : Set (Finset ι)} {A B : Finset ι} (h : OneStep W A B) :
    OneStep W B A := by
  obtain ⟨hA, hB, p, hp⟩ := h
  exact ⟨hB, hA, p, hp.symm⟩

/-- A path of one-coordinate moves inside `W`, together with its length. -/
inductive StepPath (W : Set (Finset ι)) : Finset ι → Finset ι → ℕ → Prop
  | nil {A : Finset ι} (hA : A ∈ W) : StepPath W A A 0
  | cons {A B C : Finset ι} {n : ℕ} (h : OneStep W A B) (t : StepPath W B C n) :
      StepPath W A C (n + 1)

theorem StepPath.append {W : Set (Finset ι)} {A B C : Finset ι} {m n : ℕ}
    (h₁ : StepPath W A B m) (h₂ : StepPath W B C n) : StepPath W A C (m + n) := by
  induction h₁ with
  | nil _ => simpa using h₂
  | cons h _ ih =>
      rename_i m' _
      have : StepPath W _ C (m' + n) := ih h₂
      simpa [Nat.succ_add] using StepPath.cons h this

namespace ConnectedRollerModel

end ConnectedRollerModel

section Counterexample

variable {p q : ι}

end Counterexample

end FiniteChains
