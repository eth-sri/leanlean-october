/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryScopeOperator
public import VaughtConjecture.Knight.ScopeBoundary

@[expose] public section

namespace VaughtConjecture.Knight.OrderedScopeRelocation

open AmalgamationPlan Transform Value ExtOrd

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B : Finset ι}

variable {D : CellScheme A} (sem : Semantics D) (hB : B ∈ D.plan) {k : ℕ}

variable (S : OrdinaryScopeOperator.Core (ScopeBoundary.rows D B hB sem) k)

abbrev shared := ScopeBoundary.scheme D B hB

abbrev leftMap := (ScopeBoundary.toCell D B hB).toEmbedding

abbrev rightMap := S.original.toEmbedding

abbrev Occ := ProfileFaceUnion.Carrier (X := Cell D) (rightMap sem hB S)

def enumeration : Occ sem hB S ≃ Fin (Fintype.card (Occ sem hB S)) :=
  ProfileBoundaryOrder.enumeration (leftMap hB) (rightMap sem hB S)
    (ScopeBoundary.toCell D B hB).strictMono S.original.strictMono

def index : Occ sem hB S → Finset ι × ℕ :=
  ProfileFaceUnion.paste (rightMap sem hB S) D.cell S.carrier.cell

theorem index_right (d : Cell S.carrier) :
    index sem hB S (ProfileFaceUnion.right (leftMap hB) (rightMap sem hB S) d) =
      S.carrier.cell d :=
  ProfileFaceUnion.paste_right _ _ (fun c => (S.index c).symm) d

theorem index_mem (z : Occ sem hB S) : index sem hB S z ∈ Plan.gradedPlan D.plan := by
  rcases ProfileFaceUnion.covered (leftMap hB) (rightMap sem hB S) z with
    ⟨d, rfl⟩ | ⟨d, rfl⟩
  · exact D.cell_mem d
  · rw [index_right]
    obtain ⟨hp, hg, hc⟩ := Plan.mem_gradedPlan.mp (S.carrier.cell_mem d)
    rw [S.plan] at hp
    exact Plan.mem_gradedPlan.mpr ⟨(Finset.mem_inter.mp hp).1, hg, hc⟩

def carrier : CellScheme A where
  plan := D.plan
  isPlan := D.isPlan
  card := Fintype.card (Occ sem hB S)
  cell c := index sem hB S ((enumeration sem hB S).symm c)
  cell_mem _ := index_mem sem hB S _

def old (d : Cell D) : Cell (carrier sem hB S) :=
  enumeration sem hB S (ProfileFaceUnion.left (rightMap sem hB S) d)

def localCell (d : Cell S.carrier) : Cell (carrier sem hB S) :=
  enumeration sem hB S (ProfileFaceUnion.right (leftMap hB) (rightMap sem hB S) d)

theorem old_index (d : Cell D) : (carrier sem hB S).cell (old sem hB S d) = D.cell d := by
  change index sem hB S ((enumeration sem hB S).symm (enumeration sem hB S _)) = _
  aesop

theorem local_index (d : Cell S.carrier) :
    (carrier sem hB S).cell (localCell sem hB S d) = S.carrier.cell d := by
  change index sem hB S ((enumeration sem hB S).symm (enumeration sem hB S _)) = _
  rw [Equiv.symm_apply_apply, index_right]

theorem old_order : StrictMono (old sem hB S) :=
  ProfileBoundaryOrder.enumeration_left _ _ _ _

theorem local_order : StrictMono (localCell sem hB S) :=
  ProfileBoundaryOrder.enumeration_right _ _ _ _

theorem shared_cell (c : Cell (shared hB)) :
    localCell sem hB S (S.original c) = old sem hB S (ScopeBoundary.toCell D B hB c) :=
  congrArg (enumeration sem hB S) (ProfileFaceUnion.right_shared _ _ c)

theorem covered (z : Cell (carrier sem hB S)) :
    (∃ d, old sem hB S d = z) ∨ ∃ e, localCell sem hB S e = z := by
  rcases ProfileFaceUnion.covered (leftMap hB) (rightMap sem hB S)
    ((enumeration sem hB S).symm z) with ⟨d, hd⟩ | ⟨e, he⟩
  · exact Or.inl ⟨d, (congrArg (enumeration sem hB S) hd).trans
      ((enumeration sem hB S).apply_symm_apply z)⟩
  · exact Or.inr ⟨e, (congrArg (enumeration sem hB S) he).trans
      ((enumeration sem hB S).apply_symm_apply z)⟩

theorem classify (z : Cell (carrier sem hB S)) :
    (∃ d, old sem hB S d = z) ∨ (carrier sem hB S).scope z = B := by
  rcases covered sem hB S z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · simp
  · rcases S.coverage e with ⟨c, rfl⟩ | hc
    · exact Or.inl ⟨ScopeBoundary.toCell D B hB c, (shared_cell sem hB S c).symm⟩
    · exact Or.inr ((congrArg Prod.fst (local_index sem hB S e)).trans hc)

theorem local_exhaustive (z : Cell (carrier sem hB S))
    (hz : (carrier sem hB S).scope z ⊆ B) : ∃ e, localCell sem hB S e = z := by
  rcases covered sem hB S z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · change ((carrier sem hB S).cell (old sem hB S d)).1 ⊆ B at hz
    rw [old_index] at hz
    obtain ⟨c, rfl⟩ := ScopeBoundary.exhaustive D B hB hz
    exact ⟨S.original c, shared_cell sem hB S c⟩
  simp

/-- Separation concerns scope containment, not a global bound on old grades. -/
def Separated : Prop := ∀ d : Cell D, ¬ B ⊆ D.scope d

variable (hsep : Separated (D := D) (B := B))

include hsep in
theorem old_exhaustive (c : Cell D) (z : Cell (carrier sem hB S))
    (hz : (carrier sem hB S).scope z ⊆ D.scope c) : ∃ d, old sem hB S d = z := by
  rcases classify sem hB S z with h | h
  · assumption
  · exact False.elim (hsep c (h ▸ hz))

def oldPatch : SemanticPatch D (carrier sem hB S) where
  map := ⟨old sem hB S, (old_order sem hB S).injective⟩
  index := old_index sem hB S
  closed c z hz := old_exhaustive sem hB S hsep c z hz.1

def localPatch : SemanticPatch S.carrier (carrier sem hB S) where
  map := ⟨localCell sem hB S, (local_order sem hB S).injective⟩
  index := local_index sem hB S
  closed c d hd := local_exhaustive sem hB S d (hd.1.trans (S.carrier.scope_subset c))

local notation "K" => carrier sem hB S
local notation "r" => localCell sem hB S

def patches : SemanticPatchUnion D S.carrier K :=
  ⟨oldPatch sem hB S hsep, localPatch sem hB S, covered sem hB S⟩

local notation "U" => patches sem hB S hsep

theorem shared_of_eq {d : Cell D} {e : Cell S.carrier}
    (he : old sem hB S d = r e) : ∃ c, ScopeBoundary.toCell D B hB c = d ∧ S.original c = e :=
  (ProfileFaceUnion.overlap (leftMap hB) (rightMap sem hB S) d e).mp ((enumeration sem hB S).injective he)

theorem agreement : (U).Agreement sem S.rows := by
  apply (U).agreement_of_shared sem S.rows (ScopeBoundary.toCell D B hB) S.original
    (fun c => (shared_cell sem hB S c).symm) (shared_of_eq sem hB S)
  · intro c d
    exact ScopeBoundary.exhaustive D B hB (d.2.1.trans (ScopeBoundary.scope_bound D B hB c))
  · exact fun c d hd => (S.row c ⟨d, hd⟩).symm

abbrev rows := (U).rows sem S.rows

theorem row_old : (U).old.Preserves sem (rows sem hB S hsep) := (U).old_row sem S.rows

theorem row_local : (U).low.Preserves S.rows (rows sem hB S hsep) :=
  (U).low_row sem S.rows (agreement sem hB S hsep)

/-- The completed scope is an exact semantic face of the installed carrier. -/
def localFace : ExactSemanticFace S.rows (rows sem hB S hsep) where
  map := ⟨r, (local_order sem hB S).injective⟩
  index := local_index sem hB S
  exhaustive := local_exhaustive sem hB S
  row := row_local sem hB S hsep

theorem consistent (hc : sem.IsConsistent) : (rows sem hB S hsep).IsConsistent :=
  (U).consistent sem S.rows (agreement sem hB S hsep) hc S.consistent

theorem coded (hc : sem.IsCoded) : (rows sem hB S hsep).IsCoded := (U).coded sem S.rows hc S.coded

end

end VaughtConjecture.Knight.OrderedScopeRelocation
