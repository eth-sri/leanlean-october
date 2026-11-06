/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryScopeOperator
public import VaughtConjecture.Knight.ScopeBoundary

/-! # Ordered relocation of a completed scope into its ambient inventory

The overlap is the actual restriction of the ambient inventory. The ordered
union identifies precisely those occurrences, not cells with equal indices.
Scope separation proves that no new cell enters any earlier owner's lower
domain. This operation does not impose a grade bound on the ambient scheme.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.OrderedScopeRelocation
open AmalgamationPlan Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A B : Finset ι}
  {D : CellScheme A} (sem : Semantics D) (hB : B ∈ D.plan) {k : ℕ}
  (S : OrdinaryScopeOperator.Core (ScopeBoundary.rows D B hB sem) k)

abbrev shared := ScopeBoundary.scheme D B hB
abbrev leftMap := (ScopeBoundary.toCell D B hB).toEmbedding
abbrev rightMap := S.original.toEmbedding
abbrev Occ := ProfileFaceUnion.Carrier (X := Cell D) (rightMap sem hB S)

local notation "lMap" => leftMap hB
local notation "rMap" => rightMap sem hB S

def enumeration : Occ sem hB S ≃ Fin (Fintype.card (Occ sem hB S)) :=
  ProfileBoundaryOrder.enumeration lMap rMap
    (ScopeBoundary.toCell D B hB).strictMono S.original.strictMono

local notation "enum" => enumeration sem hB S
local notation "enumSymm" => Equiv.symm (enumeration sem hB S)

def index : Occ sem hB S → Finset ι × ℕ :=
  ProfileFaceUnion.paste rMap D.cell S.carrier.cell

local notation "idx" => index sem hB S

theorem index_right (d : Cell S.carrier) :
    idx (ProfileFaceUnion.right lMap rMap d) = S.carrier.cell d :=
  ProfileFaceUnion.paste_right _ _ (fun c => (S.index c).symm) d

def carrier : CellScheme A where
  plan := D.plan
  isPlan := D.isPlan
  card := Fintype.card (Occ sem hB S)
  cell c := idx (enumSymm c)
  cell_mem c := by
    generalize enumSymm c = z
    rcases ProfileFaceUnion.covered lMap rMap z with ⟨d, rfl⟩ | ⟨d, rfl⟩
    · exact D.cell_mem d
    · rw [index_right]
      obtain ⟨hp, hg, hc⟩ := Plan.mem_gradedPlan.mp (S.carrier.cell_mem d)
      rw [S.plan] at hp
      exact Plan.mem_gradedPlan.mpr ⟨(Finset.mem_inter.mp hp).1, hg, hc⟩

def old (d : Cell D) : Cell (carrier sem hB S) :=
  enum (ProfileFaceUnion.left rMap d)

def localCell (d : Cell S.carrier) : Cell (carrier sem hB S) :=
  enum (ProfileFaceUnion.right lMap rMap d)

local notation "K" => carrier sem hB S
local notation "Kcell" => CellScheme.cell (carrier sem hB S)
local notation "Kscope" => CellScheme.scope (carrier sem hB S)
local notation "Kgrade" => CellScheme.grade (carrier sem hB S)
local notation "Kbelow" => CellScheme.below (carrier sem hB S)
local notation "l" => old sem hB S
local notation "r" => localCell sem hB S

theorem old_index (d : Cell D) : Kcell (l d) = D.cell d := by
  change idx (enumSymm (enum _)) = _
  rw [Equiv.symm_apply_apply]; rfl

theorem local_index (d : Cell S.carrier) : Kcell (r d) = S.carrier.cell d := by
  change idx (enumSymm (enum _)) = _
  rw [Equiv.symm_apply_apply, index_right]

theorem old_order : StrictMono l :=
  ProfileBoundaryOrder.enumeration_left _ _ _ _

theorem local_order : StrictMono r :=
  ProfileBoundaryOrder.enumeration_right _ _ _ _

theorem shared_cell (c : Cell (shared hB)) :
    r (S.original c) = l (ScopeBoundary.toCell D B hB c) :=
  congrArg enum (ProfileFaceUnion.right_shared _ _ c)

theorem covered (z : Cell K) : (∃ d, l d = z) ∨ ∃ e, r e = z := by
  rcases ProfileFaceUnion.covered lMap rMap (enumSymm z) with ⟨d, hd⟩ | ⟨e, he⟩
  · exact Or.inl ⟨d, (congrArg enum hd).trans (Equiv.apply_symm_apply _ z)⟩
  · exact Or.inr ⟨e, (congrArg enum he).trans (Equiv.apply_symm_apply _ z)⟩

theorem classify (z : Cell K) : (∃ d, l d = z) ∨ Kscope z = B := by
  rcases covered sem hB S z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · exact Or.inl ⟨d, rfl⟩
  · rcases S.coverage e with ⟨c, rfl⟩ | hc
    · exact Or.inl ⟨ScopeBoundary.toCell D B hB c, (shared_cell sem hB S c).symm⟩
    · exact Or.inr ((congrArg Prod.fst (local_index sem hB S e)).trans hc)

theorem local_exhaustive (z : Cell K) (hz : Kscope z ⊆ B) : ∃ e, r e = z := by
  rcases covered sem hB S z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · change (Kcell (l d)).1 ⊆ B at hz
    rw [old_index] at hz
    obtain ⟨c, rfl⟩ := ScopeBoundary.exhaustive D B hB hz
    exact ⟨S.original c, shared_cell sem hB S c⟩
  · exact ⟨e, rfl⟩

def Separated : Prop := ∀ d : Cell D, ¬ B ⊆ D.scope d

variable (hsep : Separated (D := D) (B := B))

include hsep in
theorem old_exhaustive (c : Cell D) (z : Cell K) (hz : Kscope z ⊆ D.scope c) :
    ∃ d, l d = z := by
  rcases classify sem hB S z with h | h
  · exact h
  · exact False.elim (hsep c (h ▸ hz))

def oldBelow (c : Cell D) : D.below (D.cell c) ≃ Kbelow (Kcell (l c)) :=
  Equiv.ofBijective (fun d => ⟨l d.1, by rw [old_index, old_index]; exact d.2⟩)
    ⟨fun _ _ h => Subtype.ext ((old_order sem hB S).injective (congrArg Subtype.val h)),
     fun z => by
       have hz := z.2.1; simp only [old_index] at hz
       obtain ⟨d, hd⟩ := old_exhaustive sem hB S hsep c z.1 hz
       exact ⟨⟨d, by simpa only [← hd, old_index] using z.2⟩, Subtype.ext hd⟩⟩

def localBelow (c : Cell S.carrier) : S.carrier.below (S.carrier.cell c) ≃ Kbelow (Kcell (r c)) :=
  Equiv.ofBijective (fun d => ⟨r d.1, by rw [local_index, local_index]; exact d.2⟩)
    ⟨fun _ _ h => Subtype.ext ((local_order sem hB S).injective (congrArg Subtype.val h)),
     fun z => by
       have hz := z.2.1; simp only [local_index] at hz
       obtain ⟨d, hd⟩ := local_exhaustive sem hB S z.1
         (hz.trans (S.carrier.isPlan.subset_of_mem (S.carrier.scope_mem_plan c)))
       exact ⟨⟨d, by simpa only [← hd, local_index] using z.2⟩, Subtype.ext hd⟩⟩

open AmalgamatedBoundaryRows (total total_below pushRow pushRow_at pushRow_outside)

def table (c : Cell K) : Cell K → ExtOrd :=
  ProfileFaceUnion.paste rMap (pushRow l sem) (pushRow r S.rows) (enumSymm c)

theorem table_old (c d : Cell D) : table sem hB S (l c) (l d) = total sem c d := by
  change ProfileFaceUnion.paste _ (pushRow l sem) (pushRow r S.rows)
    (enumSymm (enum (ProfileFaceUnion.left _ c))) (l d) = _
  rw [Equiv.symm_apply_apply]
  exact pushRow_at l (old_order sem hB S).injective sem c d

include hsep in
theorem table_local (c d : Cell S.carrier) :
    table sem hB S (r c) (r d) = total S.rows c d := by
  change ProfileFaceUnion.paste _ (pushRow l sem) (pushRow r S.rows)
    (enumSymm (enum (ProfileFaceUnion.right lMap _ c))) (r d) = _
  rw [Equiv.symm_apply_apply, ProfileFaceUnion.paste_right _ _ fun c => by
    dsimp [leftMap, rightMap]
    funext z
    by_cases hz : GradedLe (Kcell z) (D.cell (ScopeBoundary.toCell D B hB c))
    · obtain ⟨d, hd⟩ := (oldBelow sem hB S hsep (ScopeBoundary.toCell D B hB c)).surjective
        ⟨z, by rw [old_index]; exact hz⟩
      obtain ⟨e, he'⟩ := ScopeBoundary.exhaustive D B hB
        (d.2.1.trans (ScopeBoundary.scope_bound D B hB c))
      have he : l d.1 = z := congrArg Subtype.val hd
      rw [← he, ← he', pushRow_at l (old_order sem hB S).injective,
        ← shared_cell, pushRow_at r (local_order sem hB S).injective]
      by_cases hde : GradedLe ((shared hB).cell e) ((shared hB).cell c)
      · exact (total_below sem (ScopeBoundary.toCell D B hB c)
          ⟨ScopeBoundary.toCell D B hB e, hde⟩).trans
          ((S.row c ⟨e, hde⟩).symm.trans (total_below S.rows (S.original c)
            ⟨S.original e, by rw [S.index, S.index]; exact hde⟩).symm)
      · exact (AmalgamatedBoundaryRows.total_outside sem
          (ScopeBoundary.toCell D B hB c) (ScopeBoundary.toCell D B hB e) hde).trans
          (AmalgamatedBoundaryRows.total_outside S.rows (S.original c) (S.original e)
            (by simpa only [S.index] using hde)).symm
    · rw [pushRow_outside l (old_order sem hB S).injective (old_index sem hB S) sem _ _ hz,
        pushRow_outside r (local_order sem hB S).injective (local_index sem hB S) S.rows]
      rwa [S.index]]
  exact pushRow_at r (local_order sem hB S).injective S.rows c d

def rows : Semantics K where
  E c d := table sem hB S c d.1
  orderly c d := by
    rcases covered sem hB S c with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · obtain ⟨e, rfl⟩ := (oldBelow sem hB S hsep c).surjective d
      change table sem hB S (l c) (l e.1) =
        extVisibilityReplace (table sem hB S (l c) (l e.1)) (Kcell (l e.1)).2 (Kcell (l e.1)).2
      rw [table_old, total_below, old_index]
      exact sem.orderly c e
    · obtain ⟨e, rfl⟩ := (localBelow sem hB S c).surjective d
      change table sem hB S (r c) (r e.1) =
        extVisibilityReplace (table sem hB S (r c) (r e.1)) (Kcell (r e.1)).2 (Kcell (r e.1)).2
      rw [table_local sem hB S hsep, total_below, local_index]
      exact S.rows.orderly c e

local notation "Rws" => rows sem hB S hsep

theorem row_old (c : Cell D) (d : D.below (D.cell c)) :
    Semantics.E Rws (l c) (oldBelow sem hB S hsep c d) = sem.E c d :=
  (table_old sem hB S c d.1).trans (total_below sem c d)

theorem row_local (c : Cell S.carrier) (d : S.carrier.below (S.carrier.cell c)) :
    Semantics.E Rws (r c) (localBelow sem hB S c d) = S.rows.E c d :=
  (table_local sem hB S hsep c d.1).trans (total_below S.rows c d)

def localFace : ExactSemanticFace S.rows Rws where
  map := ⟨r, (local_order sem hB S).injective⟩
  index := local_index sem hB S
  exhaustive := local_exhaustive sem hB S
  row := row_local sem hB S hsep

theorem consistent (hc : sem.IsConsistent) : Semantics.IsConsistent Rws := by
  intro z
  rcases covered sem hB S z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have h := respects_iff_of_equiv (sem' := sem) (sem := Rws)
      (oldBelow sem hB S hsep c) (fun d => (congrArg Prod.snd (old_index sem hB S d.1)).symm)
      (fun d e => by
        change D.scope d.1 ⊆ D.scope e.1 ↔ (Kcell (l d.1)).1 ⊆ (Kcell (l e.1)).1
        rw [old_index, old_index]; rfl)
      (fun c d _ => (row_old sem hB S hsep c.1 d).symm) (sem.E c)
    have he : sem.E c ∘ (oldBelow sem hB S hsep c).symm = Semantics.E Rws (l c) := by
      funext d
      obtain ⟨e, rfl⟩ := (oldBelow sem hB S hsep c).surjective d
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
      exact (row_old sem hB S hsep c e).symm
    rw [he] at h
    exact h.mp (hc c)
  · exact (localFace sem hB S hsep).consistent_at S.consistent c

theorem coded (hc : sem.IsCoded) : Semantics.IsCoded Rws := by
  intro z d
  rcases covered sem hB S z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · obtain ⟨e, rfl⟩ := (oldBelow sem hB S hsep c).surjective d
    change IsCodedLabel (Kcell (l c)).2 (Semantics.E Rws (l c) _)
    rw [row_old, old_index]
    exact hc c e
  · exact (localFace sem hB S hsep).coded_at S.coded c d
