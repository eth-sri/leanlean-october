/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourceLayerCarrier

@[expose] public section

namespace VaughtConjecture.Knight.ScopeReplicationCarrier

open AmalgamationPlan Transform Value ExtOrd

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

def Mixed (B C U : Finset ι) : Prop := ¬ U ⊆ B ∧ ¬ U ⊆ C

/-- Replication uses one prototype scheme with fixed original sides. -/
structure Frame (A : Finset ι) where
  base : CellScheme A
  left : Finset ι
  right : Finset ι
  covered : ∀ c : Cell base, base.scope c ≠ A → base.scope c ⊆ left ∨ base.scope c ⊆ right
  sem : Semantics base

variable (S : Frame A)

local notation "D" => S.base
local notation "B" => S.left
local notation "C" => S.right

abbrev Copy := {p : (↑(D).plan) × Cell D //
  p.1.1 ≠ A ∧ Mixed B C p.1.1 ∧ (D).scope p.2 = A ∧ (D).grade p.2 ≤ p.1.1.card}

instance : Fintype (Copy S) := Fintype.ofFinite _

def scheme : CellScheme A where
  plan := (D).plan
  isPlan := (D).isPlan
  card := (D).card + Fintype.card (Copy S)
  cell := Fin.addCases (D).cell (fun i =>
    let p := (Fintype.equivFin (Copy S)).symm i
    (p.1.1.1, (D).grade p.1.2))
  cell_mem c := by
    refine Fin.addCases ?_ ?_ c
    · intro d; simpa [Fin.addCases_left] using (D).cell_mem d
    · intro i
      simp only [Fin.addCases_right]
      let p := (Fintype.equivFin (Copy S)).symm i
      exact Plan.mem_gradedPlan.mpr ⟨p.1.1.2, (D).grade_pos _, by lia⟩

def enumeration : (Cell D ⊕ Copy S) ≃ Cell (scheme S) :=
  (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin (Copy S))).trans finSumFinEquiv

abbrev old (d : Cell D) : Cell (scheme S) := enumeration S (.inl d)

abbrev added (p : Copy S) : Cell (scheme S) := enumeration S (.inr p)

theorem old_index (d : Cell D) : (scheme S).cell (old S d) = (D).cell d := by
  change (scheme S).cell (Fin.castAdd (Fintype.card (Copy S)) d) = (D).cell d
  unfold scheme
  simp only [Fin.addCases_left]

theorem added_index (p : Copy S) :
    (scheme S).cell (added S p) = (p.1.1.1, (D).grade p.1.2) := by
  change (scheme S).cell (Fin.natAdd (D).card (Fintype.equivFin (Copy S) p)) = _
  unfold scheme
  simp

theorem old_order : StrictMono (old S) := Fin.strictMono_castAdd _

theorem cases (d : Cell (scheme S)) :
    (∃ c, d = old S c) ∨ ∃ p, d = added S p := by
  obtain ⟨x, rfl⟩ := (enumeration S).surjective d
  grind

def erase (d : Cell (scheme S)) : Cell D :=
  match (enumeration S).symm d with
  | .inl c => c
  | .inr p => p.1.2

@[simp] theorem erase_old (d : Cell D) : erase S (old S d) = d := by
  simp only [erase, old, Equiv.symm_apply_apply]

@[simp] theorem erase_added (p : Copy S) : erase S (added S p) = p.1.2 := by
  simp only [erase, added, Equiv.symm_apply_apply]

theorem erase_grade (d : Cell (scheme S)) :
    (D).grade (erase S d) = (scheme S).grade d := by
  rcases cases S d with ⟨c, rfl⟩ | ⟨p, rfl⟩
  · rw [erase_old]; exact (congrArg Prod.snd (old_index S c)).symm
  · rw [erase_added]; exact (congrArg Prod.snd (added_index S p)).symm

theorem erase_scope_of_ne (d : Cell (scheme S)) (h : (D).scope (erase S d) ≠ A) :
    (D).scope (erase S d) = (scheme S).scope d := by
  rcases cases S d with ⟨c, rfl⟩ | ⟨p, rfl⟩
  · rw [erase_old]; exact (congrArg Prod.fst (old_index S c)).symm
  aesop

theorem scope_le_erase (d : Cell (scheme S)) :
    (scheme S).scope d ⊆ (D).scope (erase S d) := by
  rcases cases S d with ⟨c, rfl⟩ | ⟨p, rfl⟩
  · rw [erase_old]
    exact (congrArg Prod.fst (old_index S c)).le
  · rw [erase_added, p.2.2.2.1]
    exact (scheme S).scope_subset _

theorem full_or_mixed (d : Cell (scheme S))
    (h : (D).scope (erase S d) = A) :
    (scheme S).scope d = A ∨ Mixed B C ((scheme S).scope d) := by
  rcases cases S d with ⟨c, rfl⟩ | ⟨p, rfl⟩
  · exact Or.inl ((congrArg Prod.fst (old_index S c)).trans
      (by simpa only [erase_old, CellScheme.scope] using h))
  · exact Or.inr (by simpa only [CellScheme.scope, added_index] using p.2.2.1)

theorem erase_le {d c : Cell (scheme S)}
    (h : GradedLe ((scheme S).cell d) ((scheme S).cell c)) :
    GradedLe ((D).cell (erase S d)) ((D).cell (erase S c)) := by
  refine ⟨?_, ?_⟩
  swap
  · change (D).grade (erase S d) ≤ (D).grade (erase S c)
    rw [erase_grade, erase_grade]
    exact h.2
  change (D).scope (erase S d) ⊆ (D).scope (erase S c)
  by_cases hc : (D).scope (erase S c) = A
  · rw [hc]; exact (D).scope_subset _
  · rw [erase_scope_of_ne S c hc]
    rcases cases S d with ⟨e, rfl⟩ | ⟨p, rfl⟩
    · simpa only [erase_old, CellScheme.scope, old_index] using h.1
    · have hs : p.1.1.1 ⊆ (D).scope (erase S c) := by
        rw [erase_scope_of_ne S c hc]
        simpa only [CellScheme.scope, added_index] using h.1
      rcases S.covered _ hc with hb | hc'
      · exact (p.2.2.1.1 (hs.trans hb)).elim
      · exact (p.2.2.1.2 (hs.trans hc')).elim

def belowErase (c : Cell (scheme S)) :
    (scheme S).below ((scheme S).cell c) → (D).below ((D).cell (erase S c)) :=
  fun d => ⟨erase S d.1, erase_le S d.2⟩

/-- New occurrences occupy formerly empty proper mixed indices. -/
theorem old_index_exhaustive (c : Cell D) (z : Cell (scheme S))
    (hz : (scheme S).cell z = (D).cell c) : ∃ d, old S d = z := by
  rcases cases S z with ⟨d, rfl⟩ | ⟨p, rfl⟩
  · exact ⟨d, rfl⟩
  · have hs : p.1.1.1 = (D).scope c := (congrArg Prod.fst (added_index S p)).symm.trans
      (congrArg Prod.fst hz)
    by_cases hc : (D).scope c = A
    · grind
    · rcases S.covered c hc with hb | hc'
      · exact (p.2.2.1.1 (hs ▸ hb)).elim
      · exact (p.2.2.1.2 (hs ▸ hc')).elim

def oldBelow (J : Finset ι × ℕ) (d : (D).below J) : (scheme S).below J :=
  ⟨old S d.1, by rw [old_index]; grind⟩

/-- Relocate a full-scope prototype to an actual mixed scope, retaining its
identity. At the full scope use its existing occurrence. -/
def atScope (U : Finset ι) (hU : U ∈ (D).plan) (hm : U = A ∨ Mixed B C U)
    (c : Cell D) (hc : (D).scope c = A) (hg : (D).grade c ≤ U.card) :
    Cell (scheme S) := by
  classical
  exact if h : U = A then old S c else
    added S ⟨(⟨U, hU⟩, c), h, hm.resolve_left h, hc, hg⟩

theorem atScope_index (U : Finset ι) (hU : U ∈ (D).plan) (hm : U = A ∨ Mixed B C U)
    (c : Cell D) (hc : (D).scope c = A) (hg : (D).grade c ≤ U.card) :
    (scheme S).cell (atScope S U hU hm c hc hg) = (U, (D).grade c) := by
  classical
  unfold atScope
  split_ifs with h
  · exact (old_index S c).trans (Prod.ext (hc.trans h.symm) rfl)
  · exact added_index S _

theorem erase_atScope (U : Finset ι) (hU : U ∈ (D).plan) (hm : U = A ∨ Mixed B C U)
    (c : Cell D) (hc : (D).scope c = A) (hg : (D).grade c ≤ U.card) :
    erase S (atScope S U hU hm c hc hg) = c := by
  classical
  unfold atScope
  split_ifs <;> simp

/-- Any original availability witness at the erased target has an actual
occurrence at that target's scope, with exactly the same prototype. -/
theorem exists_at_index (t : Cell (scheme S)) (w : Cell D)
    (hw : (D).cell w = (D).cell (erase S t)) :
    ∃ z : Cell (scheme S),
      (scheme S).cell z = (scheme S).cell t ∧ erase S z = w := by
  by_cases ht : (D).scope (erase S t) = A
  · have hws : (D).scope w = A := by simp_all
    have hwg : (D).grade w = (scheme S).grade t :=
      (congrArg Prod.snd hw).trans (erase_grade S t)
    let z := atScope S ((scheme S).scope t) ((scheme S).scope_mem_plan t)
      (full_or_mixed S t ht) w hws (hwg ▸ (scheme S).grade_le_card_scope t)
    refine ⟨z, ?_, erase_atScope S _ _ _ _ _ _⟩
    exact (atScope_index S _ _ _ _ _ _).trans (by rw [hwg]; rfl)
  · refine ⟨old S w, (old_index S w).trans (hw.trans ?_), erase_old S w⟩
    exact Prod.ext (erase_scope_of_ne S t ht) (erase_grade S t)

/-- A full or mixed index has only full-scope prototypes. -/
theorem erase_index {U : Finset ι} {j : ℕ} (hm : U = A ∨ Mixed B C U)
    (c : Cell (scheme S)) (hc : (scheme S).cell c = (U, j)) :
    (D).cell (erase S c) = (A, j) := by
  apply Prod.ext
  · change (D).scope (erase S c) = A
    by_contra hne
    have hs : (D).scope (erase S c) = U :=
      (erase_scope_of_ne S c hne).trans (congrArg Prod.fst hc)
    rcases hm with rfl | hm
    · exact hne hs
    · rcases S.covered _ hne with hb | hc'
      · exact hm.1 (hs ▸ hb)
      · exact hm.2 (hs ▸ hc')
  · change (D).grade (erase S c) = j
    exact (erase_grade S c).trans (congrArg Prod.snd hc)

/-- Place a prototype on a mixed cutoff. -/
def replica {U : Finset ι} {j : ℕ} (hU : U ∈ (D).plan)
    (hm : U = A ∨ Mixed B C U) (hj : j ≤ U.card)
    (c : Cell D) (hc : (D).scope c = A) (hg : (D).grade c ≤ j) :
    (scheme S).below (U, j) :=
  ⟨atScope S U hU hm c hc (hg.trans hj),
    (atScope_index S U hU hm c hc (hg.trans hj)) ▸ ⟨le_rfl, hg⟩⟩

theorem replica_index {U j} (hU : U ∈ (D).plan) (hm : U = A ∨ Mixed B C U) (hj : j ≤ U.card)
    (c) (hc) (hg) :
    (scheme S).cell (replica S hU hm hj c hc hg).1 = (U, (D).grade c) :=
  atScope_index S U hU hm c hc (hg.trans hj)

theorem erase_replica {U j} (hU : U ∈ (D).plan) (hm : U = A ∨ Mixed B C U) (hj : j ≤ U.card)
    (c) (hc) (hg) : erase S (replica S hU hm hj c hc hg).1 = c :=
  erase_atScope S U hU hm c hc (hg.trans hj)

end

end VaughtConjecture.Knight.ScopeReplicationCarrier
