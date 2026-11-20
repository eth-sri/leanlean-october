/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RecursiveSourceCarrier
public import VaughtConjecture.Knight.CanonicalPairBoundary

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveInventory

open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (sem : Semantics D)

abbrev UpperProfile (j : ℕ) := CanonicalFieldLayer.Profile (GradeCutBoundary.rows D j sem)
  j (Cell D) (GradeCutBoundary.toCell D j)

def Profile : ℕ → Type 1
  | 0 => PUnit
  | 1 => CanonicalPairBoundary.firstProfiles sem 1 2
  | 2 => CanonicalPairBoundary.secondProfiles sem 2
  | n + 3 => UpperProfile sem (n + 3)

instance (j : ℕ) : Fintype (Profile sem j) := by
  rcases j with _ | _ | _ | j <;> dsimp only [Profile] <;> infer_instance

abbrev scheme (n : ℕ) (hn : n ≤ A.card) := RecursiveSourceCarrier.scheme D (Profile sem) n hn

abbrev boundary (n : ℕ) (hn : n ≤ A.card) :=
  RecursiveSourceCarrier.boundary D (Profile sem) n hn

theorem boundary_cell (n : ℕ) (hn : n ≤ A.card) (d : Cell D) :
    (scheme sem n hn).cell (boundary sem n hn d) = D.cell d :=
  RecursiveSourceCarrier.boundary_cell D (Profile sem) n hn d

theorem proper_occurrence (n : ℕ) (hn : n ≤ A.card) (z : Cell (scheme sem n hn))
    (hz : ¬ A ⊆ (scheme sem n hn).scope z) : ∃ d, boundary sem n hn d = z := by
  rcases RecursiveSourceCarrier.classify D (Profile sem) n hn z with h | ⟨j, _, _, he⟩
  · exact h
  simp_all

theorem proper_below (n : ℕ) (hn : n ≤ A.card) (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1)
    (z : Cell (scheme sem n hn)) (hz : GradedLe ((scheme sem n hn).cell z) J) :
    ∃ d, boundary sem n hn d = z :=
  proper_occurrence sem n hn z (fun h => hJ (h.trans hz.1))

def patch (hp : ∀ d : Cell D, D.scope d ≠ A) (n : ℕ) (hn : n ≤ A.card) :
    SemanticPatch D (scheme sem n hn) where
  map := (boundary sem n hn).toEmbedding
  index := boundary_cell sem n hn
  closed c := proper_below sem n hn _ (fun h => hp c (Finset.Subset.antisymm (D.scope_subset c) h))

/-- Normalize from the actual current old lower domain; future fields are
retained in the vector but are not required to be lawful at absent owners. -/
def encode (n : ℕ) {p : Cell D → ExtOrd}
    (hp : RespectsSemanticsBelow sem (A, n + 3) (fun d => p d.1)) (ht : ∀ d, p d ≠ ⊤) :
    Profile sem (n + 3) := by
  let j := n + 3
  have hr := GradeCutBoundary.pullback_respects D j sem le_rfl hp
  apply CanonicalFieldLayer.encode (GradeCutBoundary.rows D j sem) j (Cell D)
    (GradeCutBoundary.toCell D j) (GradeCutBoundary.grade_bound D j) _ ht
  exact hr.toRespects (fun d =>
    ⟨D.scope_subset _, GradeCutBoundary.grade_bound D j d⟩)

theorem separated (hp : ∀ d : Cell D, D.scope d ≠ A)
    (n : ℕ) (hn : n ≤ A.card) (d : Cell (scheme sem n hn)) :
    ¬ GradedLe (A, n + 1) ((scheme sem n hn).cell d) :=
  RecursiveSourceCarrier.separated D (Profile sem) hp n hn d

end

end VaughtConjecture.Knight.CanonicalRecursiveInventory
