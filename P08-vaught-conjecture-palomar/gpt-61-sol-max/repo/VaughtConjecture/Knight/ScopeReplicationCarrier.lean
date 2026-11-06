/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.SourceLayerCarrier

/-! # Replicating full-scope auxiliary occurrences at mixed scopes

Keep the entire original enumeration and append one scope-tagged copy of each
full-scope cell at every proper mixed plan scope permitting its grade. Erasing
a scope tag preserves the grade, but need not preserve the scope. Original
proper owners retain their domains; auxiliary owners acquire new arguments.
No semantic or lifting hypothesis enters this finite carrier construction.
-/

namespace VaughtConjecture.Knight.ScopeReplicationCarrier
open AmalgamationPlan
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
  (D : CellScheme A) (B C : Finset ι)

def Mixed U := ¬ U ⊆ B ∧ ¬ U ⊆ C

abbrev Copy := {p : (↑D.plan) × Cell D //
  p.1.1 ≠ A ∧ Mixed B C p.1.1 ∧ D.scope p.2 = A ∧ D.grade p.2 ≤ p.1.1.card}

local notation "Copy₀" => Copy D B C

instance : Fintype (Copy₀) := Fintype.ofFinite _

def scheme : CellScheme A where
  plan := D.plan
  isPlan := D.isPlan
  card := D.card + Fintype.card Copy₀
  cell := Fin.addCases D.cell (fun i =>
    let p := (Fintype.equivFin Copy₀).symm i
    (p.1.1.1, D.grade p.1.2))
  cell_mem c := by
    refine Fin.addCases ?_ ?_ c
    · intro d; simpa only [Fin.addCases_left] using D.cell_mem d
    · intro i
      simp only [Fin.addCases_right]
      let p := (Fintype.equivFin Copy₀).symm i
      exact Plan.mem_gradedPlan.mpr ⟨p.1.1.2, D.grade_pos _, p.2.2.2.2⟩

local notation "scheme₀" => scheme D B C

def enumeration : (Cell D ⊕ Copy₀) ≃ Cell (scheme₀) :=
  (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin (Copy₀))).trans finSumFinEquiv

abbrev old d := enumeration D B C (.inl d)
abbrev added p := enumeration D B C (.inr p)

local notation "old₀" => old D B C

variable {D B C} in
theorem old_index d : (scheme₀).cell (old₀ d) = D.cell d := by
  change (scheme₀).cell (Fin.castAdd (Fintype.card Copy₀) d) = D.cell d
  unfold scheme
  simp  

theorem added_index p :
    (scheme₀).cell (added D B C p) = (p.1.1.1, D.grade p.1.2) := by
  change (scheme₀).cell (Fin.natAdd D.card (Fintype.equivFin Copy₀ p)) = _
  unfold scheme
  simp  

theorem old_order : StrictMono (old₀) := Fin.strictMono_castAdd _

variable {D B C} in
theorem cases d :
    (∃ c, d = old₀ c) ∨ ∃ p, d = added D B C p := by
  obtain ⟨x, rfl⟩ := (enumeration D B C).surjective d
  cases x with
  | inl c => exact Or.inl ⟨c, rfl⟩
  | inr p => exact Or.inr ⟨p, rfl⟩

def erase d :=
  match (enumeration D B C).symm d with
  | .inl c => c
  | .inr p => p.1.2

local notation "erase₀" => erase D B C

@[simp] theorem erase_old d : erase₀ (old₀ d) = d := by
  simp  [erase,  ]

@[simp] theorem erase_added p : erase₀ (added D B C p) = p.1.2 := by
  simp  [erase,  ]

local notation "old_index₀" => old_index

theorem erase_grade d :
    D.grade (erase₀ d) = (scheme₀).grade d := by
  rcases cases d with ⟨c, rfl⟩ | ⟨p, rfl⟩
  · rw [erase_old]; exact (congrArg Prod.snd (old_index₀ c)).symm
  · rw [erase_added]; exact (congrArg Prod.snd (added_index D B C p)).symm

theorem erase_scope_of_ne d (h : D.scope (erase₀ d) ≠ A) :
    D.scope (erase₀ d) = (scheme₀).scope d := by
  rcases cases d with ⟨c, rfl⟩ | ⟨p, rfl⟩
  · rw [erase_old]; exact (congrArg Prod.fst (old_index₀ c)).symm
  · aesop

theorem scope_le_erase d :
    (scheme₀).scope d ⊆ D.scope (erase₀ d) := by
  rcases cases d with ⟨c, rfl⟩ | ⟨p, rfl⟩
  · rw [erase_old]
    exact (congrArg Prod.fst (old_index₀ c)).le
  · rw [erase_added, p.2.2.2.1]
    exact (scheme₀).scope_subset _

theorem full_or_mixed d
    (h : D.scope (erase₀ d) = A) :
    (scheme₀).scope d = A ∨ Mixed B C ((scheme₀).scope d) := by
  rcases cases d with ⟨c, rfl⟩ | ⟨p, rfl⟩
  · exact Or.inl ((congrArg Prod.fst (old_index₀ c)).trans
      (by simp_all))
  · grind [CellScheme.scope, added_index]

variable (hcover : ∀ c , D.scope c ≠ A → D.scope c ⊆ B ∨ D.scope c ⊆ C)

include hcover in
theorem erase_le {d c}
    (h : GradedLe ((scheme₀).cell d) ((scheme₀).cell c)) :
    GradedLe (D.cell (erase₀ d)) (D.cell (erase₀ c)) := by
  refine ⟨?_, ?_⟩
  swap
  · change D.grade (erase₀ d) ≤ D.grade (erase₀ c)
    rw [erase_grade, erase_grade]
    exact h.2
  change D.scope (erase₀ d) ⊆ D.scope (erase₀ c)
  by_cases hc : D.scope (erase₀ c) = A
  · rw [hc]; exact D.scope_subset _
  · rw [erase_scope_of_ne D B C c hc]
    rcases cases d with ⟨e, rfl⟩ | ⟨p, rfl⟩
    · simpa only [erase_old, CellScheme.scope, old_index] using h.1
    · have hs : p.1.1.1 ⊆ D.scope (erase₀ c) := by
        rw [erase_scope_of_ne D B C c hc]
        simpa only [CellScheme.scope, added_index] using h.1
      rcases hcover _ hc with hb | hc'
      · exact (p.2.2.1.1 (hs.trans hb)).elim
      · exact (p.2.2.1.2 (hs.trans hc')).elim

def belowErase c :
    (scheme₀).belowCell c → D.below (D.cell (erase₀ c)) :=
  fun d => ⟨erase₀ d.1, erase_le D B C hcover d.2⟩

include hcover in
/-- New occurrences occupy formerly empty proper mixed indices. -/
theorem old_index_exhaustive c z
    (hz : (scheme₀).cell z = D.cell c) : ∃ d, old₀ d = z := by
  rcases cases z with ⟨d, rfl⟩ | ⟨p, rfl⟩
  · exact ⟨d, rfl⟩
  · have hs : p.1.1.1 = D.scope c := (congrArg Prod.fst (added_index D B C p)).symm.trans
      (congrArg Prod.fst hz)
    by_cases hc : D.scope c = A
    · exact (p.2.1 (hs.trans hc)).elim
    · rcases hcover c hc with hb | hc'
      · exact (p.2.2.1.1 (hs ▸ hb)).elim
      · exact (p.2.2.1.2 (hs ▸ hc')).elim

def oldBelow J (d : D.below J) : (scheme₀).below J :=
  ⟨old₀ d.1, by rw [old_index]; exact d.2⟩

/-- Relocate a full-scope prototype to an actual mixed scope, retaining its
identity. At the full scope use its existing occurrence. -/
def atScope U (hU : U ∈ D.plan) (hm : U = A ∨ Mixed B C U)
    c (hc : D.scope c = A) (hg : D.grade c ≤ U.card) :=  if h : U = A then old₀ c else
    added D B C ⟨(⟨U, hU⟩, c), h, hm.resolve_left h, hc, hg⟩

theorem atScope_index U (hU : U ∈ D.plan) (hm : U = A ∨ Mixed B C U)
    c (hc : D.scope c = A) (hg : D.grade c ≤ U.card) :
    (scheme₀).cell (atScope D B C U hU hm c hc hg) = (U, D.grade c) := by
  
  unfold atScope
  split_ifs with h
  · exact (old_index₀ c).trans (Prod.ext (hc.trans h.symm) rfl)
  · exact added_index D B C _

theorem erase_atScope U (hU : U ∈ D.plan) (hm : U = A ∨ Mixed B C U)
    c (hc : D.scope c = A) (hg : D.grade c ≤ U.card) :
    erase₀ (atScope D B C U hU hm c hc hg) = c := by
  classical
  unfold atScope
  split_ifs <;> simp  

/-- Any original availability witness at the erased target has an actual
occurrence at that target's scope, with exactly the same prototype. -/
theorem exists_at_index t w
    (hw : D.cell w = D.cell (erase₀ t)) :
    ∃ z ,
      (scheme₀).cell z = (scheme₀).cell t ∧ erase₀ z = w := by
  by_cases ht : D.scope (erase₀ t) = A
  · have hws : D.scope w = A := (congrArg Prod.fst hw).trans ht
    have hwg : D.grade w = (scheme₀).grade t :=
      (congrArg Prod.snd hw).trans (erase_grade D B C t)
    let z := atScope D B C ((scheme₀).scope t) ((scheme₀).scope_mem_plan t)
      (full_or_mixed D B C t ht) w hws (hwg ▸ (scheme₀).grade_le_card_scope t)
    refine ⟨z, ?_, erase_atScope D B C _ _ _ _ _ _⟩
    exact (atScope_index D B C _ _ _ _ _ _).trans (by rw [hwg]; rfl)
  · refine ⟨old₀ w, (old_index₀ w).trans (hw.trans ?_), erase_old D B C w⟩
    exact Prod.ext (erase_scope_of_ne D B C t ht) (erase_grade D B C t)

