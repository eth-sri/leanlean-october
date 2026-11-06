/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.HighLayerBountiful
public import VaughtConjecture.Knight.CanonicalGradeCutSections

/-! # A recursive full-layer inventory over one unchanged proper boundary

Stage n contains the complete old boundary and every controller inventory
at grades 1 through n. Old higher-grade proper owners are never discarded.
This module constructs geometry, not consistent source rows or bountifulness.
-/

@[expose] public section

namespace VaughtConjecture.Knight.RecursiveSourceCarrier
open Transform Value ExtOrd
open scoped BigOperators
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (Q : ℕ → Type*) [∀ j, Fintype (Q j)]

def scheme : (n : ℕ) → n ≤ A.card → CellScheme A
  | 0, _ => D
  | n + 1, hn => SourceLayerCarrier.scheme (scheme n (Nat.le_of_succ_le hn))
      (Q (n + 1)) (n + 1) (Nat.succ_pos n) hn

section
variable (n : ℕ) (hn : n + 1 ≤ A.card)

def step  :
    Cell (scheme D Q n (Nat.le_of_succ_le hn)) ↪o Cell (scheme D Q (n + 1) hn) :=
  OrderEmbedding.ofStrictMono
    (fun d => SourceLayerCarrier.toCell (scheme D Q n (Nat.le_of_succ_le hn))
      (Q (n + 1)) (n + 1) (Nat.succ_pos n) hn (.inl d))
    (SourceLayerCarrier.old_order _ _ _ _ _)

theorem step_cell d :
    (scheme D Q (n + 1) hn).cell (step D Q n hn d) =
      (scheme D Q n (Nat.le_of_succ_le hn)).cell d :=
  SourceLayerCarrier.cell_toCell _ _ _ _ _ (.inl d)

end

def embed (m : ℕ) (hm : m ≤ A.card) : (t : ℕ) → (h : m + t ≤ A.card) →
    Cell (scheme D Q m hm) ↪o Cell (scheme D Q (m + t) h)
  | 0, _ => OrderEmbedding.ofStrictMono id strictMono_id
  | t + 1, h => (embed m hm t (by omega)).trans (step D Q (m + t) h)

theorem embed_cell m hm t h
    d :
    (scheme D Q (m + t) h).cell (embed D Q m hm t h d) = (scheme D Q m hm).cell d := by
  induction t with
  | zero => rfl
  | succ t ih => exact (step_cell D Q (m + t) h _).trans (ih (by omega))

def boundary : (n : ℕ) → (hn : n ≤ A.card) → Cell D ↪o Cell (scheme D Q n hn)
  | 0, _ => OrderEmbedding.ofStrictMono id strictMono_id
  | n + 1, hn => (boundary n (Nat.le_of_succ_le hn)).trans (step D Q n hn)

section
variable (n : ℕ)

theorem boundary_cell hn d :
    (scheme D Q n hn).cell (boundary D Q n hn d) = D.cell d := by
  induction n with
  | zero => rfl
  | succ n ih => exact (step_cell D Q n hn _).trans (ih (Nat.le_of_succ_le hn))

section
variable (hn : n + 1 ≤ A.card) (q : Q (n + 1))

abbrev controller  :=
  SourceLayerCarrier.controller (scheme D Q n (Nat.le_of_succ_le hn))
    (Q (n + 1)) (n + 1) (Nat.succ_pos n) hn q

theorem controller_cell  :
    (scheme D Q (n + 1) hn).cell (controller D Q n hn q).1 = (A, n + 1) :=
  (controller D Q n hn q).2

end

end

section
variable (n t : ℕ) (h : n + 1 + t ≤ A.card) (q : Q (n + 1))

/-- A controller remains a distinct actual occurrence at every later stage. -/
def retained  :
    Cell (scheme D Q (n + 1 + t) h) :=
  embed D Q (n + 1) (by omega) t h (controller D Q n (by omega) q).1

theorem retained_cell  :
    (scheme D Q (n + 1 + t) h).cell (retained D Q n t h q) = (A, n + 1) :=
  (embed_cell D Q (n + 1) (by omega) t h _).trans (controller_cell D Q n (by omega) q)

end

theorem classify n hn d :
    (∃ c, boundary D Q n hn c = d) ∨
      ∃ j, 0 < j ∧ j ≤ n ∧ (scheme D Q n hn).cell d = (A, j) := by
  induction n with
  | zero => exact Or.inl ⟨d, rfl⟩
  | succ n ih =>
    obtain ⟨x, rfl⟩ := (SourceLayerCarrier.enumeration
      (scheme D Q n (Nat.le_of_succ_le hn)) (Q (n + 1)) (n + 1) (Nat.succ_pos n) hn).surjective d
    cases x with
    | inl d =>
      rcases ih (Nat.le_of_succ_le hn) d with ⟨c, hc⟩ | ⟨j, hj, hjn, hd⟩
      · aesop
      · exact Or.inr ⟨j, hj, hjn.trans (Nat.le_succ n), (step_cell D Q n hn d).trans hd⟩
    | inr q => exact Or.inr ⟨n + 1, Nat.succ_pos n, le_rfl, controller_cell D Q n hn q⟩

theorem full_grade (hp : ∀ d, D.scope d ≠ A)
    n hn d
    (hd : (scheme D Q n hn).scope d = A) : (scheme D Q n hn).grade d ≤ n := by
  rcases classify D Q n hn d with ⟨c, rfl⟩ | ⟨j, _, hj, he⟩
  · exact (hp c ((congrArg Prod.fst (boundary_cell D Q n hn c)).symm.trans hd)).elim
  · simp_all

/-- Proper old owners may be higher than the next layer. Separation comes
from their scope, not an incorrect whole-predecessor grade bound. -/
theorem separated (hp : ∀ d, D.scope d ≠ A)
    n hn (d : Cell (scheme D Q n hn)) :
    ¬ GradedLe (A, n + 1) ((scheme D Q n hn).cell d) := by
  intro h
  have hs := Finset.Subset.antisymm
    ((scheme D Q n hn).isPlan.subset_of_mem ((scheme D Q n hn).scope_mem_plan d)) h.1
  exact (Nat.not_succ_le_self n) (h.2.trans (full_grade D Q hp n hn d hs))

end
end VaughtConjecture.Knight.RecursiveSourceCarrier
