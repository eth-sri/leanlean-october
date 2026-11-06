/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.OrdinaryScopeOperator
import VaughtConjecture.Knight.ScopeBoundary

/-! # Ordered relocation of a completed scope into its ambient inventory

The overlap is the actual restriction of the ambient inventory. The ordered
union identifies precisely those occurrences, not cells with equal indices.
Scope separation proves that no new cell enters any earlier owner's lower
domain. This operation does not impose a grade bound on the ambient scheme.
-/

namespace VaughtConjecture.Knight.OrderedScopeRelocation
open AmalgamationPlan  Value ExtOrd
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B : Finset ι}
variable {D : CellScheme A} (sem : Semantics D) (hB : B ∈ D.plan) {k : ℕ}
variable (S : OrdinaryScopeOperator.Core (ScopeBoundary.rows D B hB sem) k)

abbrev shared := ScopeBoundary.scheme D B hB
local notation "toCell₀" => ScopeBoundary.toCell D B hB

abbrev leftMap := (toCell₀).toEmbedding
abbrev rightMap := S.original.toEmbedding
local notation "rightMap₀" => rightMap sem hB S

abbrev Occ := ProfileFaceUnion.Carrier (X := Cell D) (rightMap₀)

local notation "Occ₀" => Occ sem hB S

def enumeration : Occ₀ ≃ Fin (Fintype.card (Occ₀)) :=
  ProfileBoundaryOrder.enumeration
    (toCell₀).strictMono S.original.strictMono

def index : Occ₀ → GradedIndex ι :=
  ProfileFaceUnion.paste (rightMap₀) D.cell S.carrier.cell

local notation "index₀" => index sem hB S

theorem index_right d :
    index₀ (ProfileFaceUnion.right (leftMap hB) (rightMap₀) d) =
      S.carrier.cell d :=
  ProfileFaceUnion.paste_right (fun c => (S.index c).symm) d

theorem index_mem z : index₀ z ∈ Plan.gradedPlan D.plan := by
  rcases ProfileFaceUnion.covered (leftMap hB) (rightMap₀) z with
    ⟨d, rfl⟩ | ⟨d, rfl⟩
  · exact D.cell_mem d
  · rw [index_right]
    obtain ⟨hp, hg, hc⟩ := Plan.mem_gradedPlan.mp (S.carrier.cell_mem d)
    rw [S.plan] at hp
    exact Plan.mem_gradedPlan.mpr ⟨(Finset.mem_inter.mp hp).1, hg, hc⟩

local notation "enumeration₀" => enumeration sem hB S

def carrier : CellScheme A where
  plan := D.plan
  isPlan := D.isPlan
  card := Fintype.card (Occ₀)
  cell c := index₀ ((enumeration₀).symm c)
  cell_mem _ := index_mem sem hB S _

local notation "carrier₀" => carrier sem hB S

def old (d : Cell D) : Cell (carrier₀) :=
  enumeration₀ (ProfileFaceUnion.left d)

def localCell (d : Cell S.carrier) : Cell (carrier₀) :=
  enumeration₀ (ProfileFaceUnion.right (leftMap hB) (rightMap₀) d)

local notation "old₀" => old sem hB S

variable {sem hB} in
theorem old_index d : (carrier₀).cell (old₀ d) = D.cell d := by
  change index₀ ((enumeration₀).symm (enumeration₀ _)) = _
  rw [Equiv.symm_apply_apply]
  rfl

local notation "localCell₀" => localCell sem hB S

theorem local_index d :
    (carrier₀).cell (localCell₀ d) = S.carrier.cell d := by
  change index₀ ((enumeration₀).symm (enumeration₀ _)) = _
  rw [Equiv.symm_apply_apply, index_right]

theorem old_order : StrictMono (old₀) :=
  ProfileBoundaryOrder.enumeration_left

theorem local_order : StrictMono (localCell₀) :=
  ProfileBoundaryOrder.enumeration_right

theorem shared_cell c :
    localCell₀ (S.original c) = old₀ (toCell₀ c) :=
  congrArg (enumeration₀) (ProfileFaceUnion.right_shared _ _ c)

variable {sem hB S} in
theorem covered z :
    (∃ d, old₀ d = z) ∨ ∃ e, localCell₀ e = z := by
  rcases ProfileFaceUnion.covered (leftMap hB) (rightMap₀)
    ((enumeration₀).symm z) with ⟨d, hd⟩ | ⟨e, he⟩
  · exact Or.inl ⟨d, (congrArg (enumeration₀) hd).trans
      ((enumeration₀).apply_symm_apply z)⟩
  · exact Or.inr ⟨e, (congrArg (enumeration₀) he).trans
      ((enumeration₀).apply_symm_apply z)⟩

theorem classify z :
    (∃ d, old₀ d = z) ∨ (carrier₀).scope z = B := by
  rcases covered z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · exact Or.inl ⟨d, rfl⟩
  · rcases S.coverage e with ⟨c, rfl⟩ | hc
    · simp_all  [shared_cell] <;> aesop
    · exact Or.inr ((congrArg Prod.fst (local_index sem hB S e)).trans hc)

theorem local_exhaustive z
    (hz : (carrier₀).scope z ⊆ B) : ∃ e, localCell₀ e = z := by
  rcases covered z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · change ((carrier₀).cell (old₀ d)).1 ⊆ B at hz
    rw [old_index] at hz
    obtain ⟨c, rfl⟩ := ScopeBoundary.exhaustive D B hB hz
    exact ⟨S.original c, shared_cell sem hB S c⟩
  · exact ⟨e, rfl⟩

/-- Separation concerns scope containment, not a global bound on old grades. -/
def Separated := ∀ d , ¬ B ⊆ D.scope d

variable (hsep : Separated (D := D) (B := B))

include hsep in
theorem old_exhaustive c z
    (hz : (carrier₀).scope z ⊆ D.scope c) : ∃ d, old₀ d = z := by
  rcases classify sem hB S z with h | h
  · exact h
  · exact False.elim (hsep c (h ▸ hz))

def oldBelow c :
    D.belowCell c ≃ (carrier₀).below ((carrier₀).cell (old₀ c)) :=
  Equiv.ofBijective (fun d => ⟨old₀ d.1, by
    grind [old_index]⟩) ⟨by
      intro d e h
      exact Subtype.ext ((old_order sem hB S).injective (congrArg Subtype.val h)), by
      intro z
      have hz := z.2.1
      simp only [old_index] at hz
      obtain ⟨d, hd⟩ := old_exhaustive sem hB S hsep c z.1 hz
      refine ⟨⟨d, ?_⟩, Subtype.ext hd⟩
      have h := z.2
      simpa only [← hd, old_index] using h⟩

local notation "local_order₀" => local_order sem hB S

def localBelow c :
    S.carrier.belowCell c ≃
      (carrier₀).below ((carrier₀).cell (localCell₀ c)) :=
  Equiv.ofBijective (fun d => ⟨localCell₀ d.1, by
    grind [local_index]⟩) ⟨by
      intro d e h
      exact Subtype.ext ((local_order₀).injective (congrArg Subtype.val h)), by
      intro z
      have hz := z.2.1
      simp only [local_index] at hz
      obtain ⟨d, hd⟩ := local_exhaustive sem hB S z.1
        (hz.trans (S.carrier.scope_subset c))
      refine ⟨⟨d, ?_⟩, Subtype.ext hd⟩
      have h := z.2
      simpa only [← hd, local_index] using h⟩

open AmalgamatedBoundaryRows (total total_below pushRow pushRow_at pushRow_outside)

local notation "K" => carrier sem hB S
local notation "l" => old sem hB S
local notation "r" => localCell sem hB S

theorem total_shared c d :
    total sem (toCell₀ c) (toCell₀ d) =
      total S.rows (S.original c) (S.original d) := by
  classical
  by_cases hd : GradedLe ((shared hB).cell d) ((shared hB).cell c)
  · exact (total_below sem (toCell₀ c)
      ⟨toCell₀ d, hd⟩).trans
      ((S.row c ⟨d, hd⟩).symm.trans (total_below S.rows (S.original c)
        ⟨S.original d, by rw [S.index, S.index]; exact hd⟩).symm)
  · exact (AmalgamatedBoundaryRows.total_outside sem hd).trans
      (AmalgamatedBoundaryRows.total_outside S.rows
        (by simpa only [S.index] using hd)).symm

local notation "oldBelow₀" => oldBelow sem hB S hsep

include hsep in
theorem pushRow_shared c :
    pushRow l sem (toCell₀ c) = pushRow r S.rows (S.original c) := by
  funext z
  by_cases hz : GradedLe ((K).cell z) (D.cell (toCell₀ c))
  · have hzl : GradedLe ((K).cell z) ((K).cell (l (toCell₀ c))) := by
      rw [old_index]; exact hz
    obtain ⟨d, hd⟩ := (oldBelow₀ (toCell₀ c)).surjective
      ⟨z, hzl⟩
    have he : l d.1 = z := congrArg Subtype.val hd
    obtain ⟨e, he'⟩ := ScopeBoundary.exhaustive D B hB
      (d.2.1.trans (ScopeBoundary.scope_bound D B hB c))
    rw [← he, ← he', pushRow_at l (old_order sem hB S).injective,
      ← shared_cell, pushRow_at r (local_order₀).injective]
    exact total_shared sem hB S c e
  · rw [pushRow_outside l (old_order sem hB S).injective (old_index S) sem _ _ hz,
      pushRow_outside r (local_order₀).injective (local_index sem hB S) S.rows]
    simpa only [S.index, ScopeBoundary.cell_eq] using hz

def table c :=
  ProfileFaceUnion.paste (rightMap₀) (pushRow l sem) (pushRow r S.rows)
    ((enumeration₀).symm c)

local notation "table₀" => table sem hB S

theorem table_old c d : table₀ (l c) (l d) = total sem c d := by
  change ProfileFaceUnion.paste _ (pushRow l sem) (pushRow r S.rows) ((enumeration₀).symm
    (enumeration₀ (ProfileFaceUnion.left c))) (l d) = _
  rw [Equiv.symm_apply_apply]
  exact pushRow_at l (old_order sem hB S).injective sem c d

include hsep in
theorem table_local c d :
    table₀ (r c) (r d) = total S.rows c d := by
  change ProfileFaceUnion.paste _ (pushRow l sem) (pushRow r S.rows) ((enumeration₀).symm
    (enumeration₀ (ProfileFaceUnion.right (leftMap hB) _ c))) (r d) = _
  rw [Equiv.symm_apply_apply, ProfileFaceUnion.paste_right
    (pushRow_shared sem hB S hsep)]
  exact pushRow_at r (local_order₀).injective S.rows c d

include hsep in
theorem table_orderly c (d : (K).belowCell c) :
    table₀ c d.1 = extVisibilityReplace (table₀ c d.1)
      ((K).grade d.1) ((K).grade d.1) := by
  rcases covered c with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · obtain ⟨e, rfl⟩ := (oldBelow₀ c).surjective d
    change table₀ (l c) (l e.1) =
      extVisibilityReplace (table₀ (l c) (l e.1)) ((K).cell (l e.1)).2 ((K).cell (l e.1)).2
    rw [table_old, total_below, old_index]
    exact sem.orderly c e
  · obtain ⟨e, rfl⟩ := (localBelow sem hB S c).surjective d
    change table₀ (r c) (r e.1) =
      extVisibilityReplace (table₀ (r c) (r e.1)) ((K).cell (r e.1)).2 ((K).cell (r e.1)).2
    rw [table_local sem hB S hsep, total_below, local_index]
    exact S.rows.orderly c e

def rows : Semantics K where
  E c d := table₀ c d.1
  orderly := table_orderly sem hB S hsep

local notation "rows₀" => rows sem hB S hsep

theorem row_old c d :
    (rows₀).E (l c) (oldBelow₀ c d) = sem.E c d :=
  (table_old sem hB S c d.1).trans (total_below sem c d)

theorem row_local c d :
    (rows₀).E (r c) (localBelow sem hB S c d) = S.rows.E c d :=
  (table_local sem hB S hsep c d.1).trans (total_below S.rows c d)

/-- The completed scope is an exact semantic face of the installed carrier. -/
def localFace : ExactSemanticFace S.rows (rows₀) := ⟨⟨r, (local_order₀).injective⟩,
local_index sem hB S,
local_exhaustive sem hB S,
row_local sem hB S hsep⟩

theorem consistent (hc : sem.IsConsistent) : (rows₀).IsConsistent := by
  intro z
  rcases covered z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have h := respects_iff_of_equiv (sem' := sem) (sem := rows₀)
      (oldBelow₀ c) (fun d => (congrArg Prod.snd (old_index S d.1)).symm)
      (fun d e => ?_) (fun c d hd => ?_) (sem.E c)
    · have he : sem.E c ∘ (oldBelow₀ c).symm =
          (rows₀).E (l c) := by
        funext d
        obtain ⟨e, rfl⟩ := (oldBelow₀ c).surjective d
        simp only [Function.comp_apply, Equiv.symm_apply_apply]
        exact (row_old sem hB S hsep c e).symm
      rw [he] at h
      exact h.mp (hc c)
    · change D.scope d.1 ⊆ D.scope e.1 ↔ ((K).cell (l d.1)).1 ⊆ ((K).cell (l e.1)).1
      rw [old_index, old_index]; rfl
    · exact (row_old sem hB S hsep c.1 d).symm
  · exact (localFace sem hB S hsep).consistent_at S.consistent c

theorem coded (hc : sem.IsCoded) : (rows₀).IsCoded := by
  intro z d
  rcases covered z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · obtain ⟨e, rfl⟩ := (oldBelow₀ c).surjective d
    change IsCodedLabel ((K).cell (l c)).2 ((rows₀).E (l c) _)
    rw [row_old, old_index]
    exact hc c e
  · exact (localFace sem hB S hsep).coded_at S.coded c d

