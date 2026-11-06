/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.AmalgamatedBoundary
import VaughtConjecture.Knight.PartialSections

/-! # Literal semantics on a uniformly ordered proper boundary

The two inherited tables are glued on their exact occurrence overlap.
No display is recoded and no faithful transformations are composed.
Only equality of the shared source rows is required for row installation.
-/

namespace VaughtConjecture.Knight.AmalgamatedBoundaryRows

open AmalgamationPlan AmalgamatedBoundaryPlan AmalgamatedBoundary
open  Value 

variable {ι : Type*} [DecidableEq ι]

open Classical in
/-- Extend a semantic row by bottom outside its actual lower domain. -/
noncomputable def total {B : Finset ι} {D : CellScheme B} (sem : Semantics D)
    (c d : Cell D) :=
  if h : GradedLe (D.cell d) (D.cell c) then sem.E c ⟨d, h⟩ else ⊥

theorem total_below {B : Finset ι} {D : CellScheme B} (sem : Semantics D)
    (c : Cell D) (d : D.belowCell c) : total sem c d.1 = sem.E c d := by
  rw [total, dite_eq_left d.2]
  exact congrArg (sem.E c) (Subtype.ext rfl)

theorem total_outside {B : Finset ι} {D : CellScheme B} (sem : Semantics D)
    {c d : Cell D} (h : ¬ GradedLe (D.cell d) (D.cell c)) : total sem c d = ⊥ := by
  simp only [total, dite_eq_right h]

section
variable {B C : Finset ι} {D : CellScheme B} {K : CellScheme C}
variable (f : Cell D → Cell K) (hf : Function.Injective f)
variable (hi : ∀ d, K.cell (f d) = D.cell d) (sem : Semantics D)

noncomputable def pushRow c :=
  Function.extend f (total sem c) (fun _ => ⊥)

include hf in
theorem pushRow_at c d : pushRow f sem c (f d) = total sem c d :=
  hf.extend_apply _ _ _

include hf hi in
theorem pushRow_outside c z
    (hz : ¬ GradedLe (K.cell z) (D.cell c)) : pushRow f sem c z = ⊥ := by
  
  by_cases h : ∃ d, f d = z
  · obtain ⟨d, rfl⟩ := h
    rw [pushRow_at f hf]
    apply total_outside
    simpa only [hi] using hz
  · exact Function.extend_apply' _ _ _ h

end

variable {A : Finset ι} (s : Step A)
variable (D : CellScheme (A.erase s.a)) (E : CellScheme (A.erase s.b))
variable {k : ℕ} (w : Overlap D E k) (hD : D.plan = s.left) (hE : E.plan = s.right)
variable (semD : Semantics D) (semE : Semantics E)

local notation "K" => scheme s D E w hD hE
local notation "l" => leftCell s D E w hD hE
local notation "r" => rightCell s D E w hD hE

/-- Source equality on all shared occurrences, including every auxiliary. -/
def Compatible :=
  ∀ i j, total semD (w.f i) (w.f j) = total semE (w.g i) (w.g j)

def shared_cell i :=
  (overlap s D E w hD hE _ _).mpr ⟨i, rfl, rfl⟩

local notation "enumeration₀" => enumeration D E w

variable {s D E w hD hE} in
theorem covered c : (∃ d, l d = c) ∨ ∃ e, r e = c := by
  rcases ProfileFaceUnion.covered w.f w.g ((enumeration₀).symm c) with
    ⟨d, hd⟩ | ⟨e, he⟩
  · exact Or.inl ⟨d, (congrArg enumeration₀ hd).trans
      ((enumeration₀).apply_symm_apply c)⟩
  · exact Or.inr ⟨e, (congrArg enumeration₀ he).trans
      ((enumeration₀).apply_symm_apply c)⟩

local notation "leftBelow₀" => leftBelow s D E w hD hE

local notation "left_order₀" => left_order

local notation "right_order₀" => right_order

theorem pushRow_shared (hc : Compatible s D E w semD semE) i :
    pushRow l semD (w.f i) = pushRow r semE (w.g i) := by
  funext z
  by_cases hz : GradedLe ((K).cell z) (D.cell (w.f i))
  · have hzl : GradedLe ((K).cell z) ((K).cell (l (w.f i))) := by
      rw [left_index]
      exact hz
    obtain ⟨d, hd⟩ := (leftBelow₀ (w.f i)).surjective ⟨z, hzl⟩
    have he : l d.1 = z := congrArg Subtype.val hd
    have hdc  := by
      have hs := d.2.1
      
      have hs' : (D.cell (w.f i)).1 ⊆ (E.cell (w.g i)).1 :=
        subset_of_eq (congrArg Prod.fst (w.shared i))
      exact hs.trans (hs'.trans (E.scope_subset _))
    obtain ⟨j, hj⟩ := w.left_exhaustive d.1 hdc
    rw [← he, ← hj, pushRow_at l (left_order₀).injective,
      shared_cell, pushRow_at r (right_order₀).injective]
    exact hc i j
  · rw [pushRow_outside l (left_order₀).injective
      (left_index s D E w hD hE) semD _ _ hz,
      pushRow_outside r (right_order₀).injective
      (right_index s D E w hD hE) semE]
    rwa [← w.shared]

noncomputable def table c :=
  ProfileFaceUnion.paste w.g (pushRow l semD) (pushRow r semE)
    ((enumeration₀).symm c)

local notation "table₀" => table s D E w hD hE semD semE

theorem table_left c d : table₀ (l c) (l d) =
    total semD c d := by
  change ProfileFaceUnion.paste w.g (pushRow l semD) (pushRow r semE)
    ((enumeration₀).symm
    (enumeration₀ (ProfileFaceUnion.left c))) (l d) = _
  rw [Equiv.symm_apply_apply]
  exact pushRow_at l (left_order₀).injective semD c d

theorem table_right (hc : Compatible s D E w semD semE) c d :
    table₀ (r c) (r d) = total semE c d := by
  change ProfileFaceUnion.paste w.g (pushRow l semD) (pushRow r semE)
    ((enumeration₀).symm
    (enumeration₀ (ProfileFaceUnion.right w.f w.g c))) (r d) = _
  rw [Equiv.symm_apply_apply, ProfileFaceUnion.paste_right
    (pushRow_shared s D E w hD hE semD semE hc)]
  exact pushRow_at r (right_order₀).injective semE c d

variable (hc : Compatible s D E w semD semE)

include hc in
theorem table_orderly c (d : (K).belowCell c) :
    table₀ c d.1 =
      extVisibilityReplace (table₀ c d.1)
        ((K).grade d.1) ((K).grade d.1) := by
  rcases covered c with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · obtain ⟨e, rfl⟩ := (leftBelow₀ c).surjective d
    change table₀ (l c) (l e.1) =
      extVisibilityReplace (table₀ (l c) (l e.1))
        ((K).cell (l e.1)).2 ((K).cell (l e.1)).2
    rw [table_left, total_below, left_index]
    exact semD.orderly c e
  · obtain ⟨e, rfl⟩ := (rightBelow s D E w hD hE c).surjective d
    change table₀ (r c) (r e.1) =
      extVisibilityReplace (table₀ (r c) (r e.1))
        ((K).cell (r e.1)).2 ((K).cell (r e.1)).2
    rw [table_right s D E w hD hE semD semE hc, total_below, right_index]
    exact semE.orderly c e

variable {s D E w semD semE} in
/-- Both rows are copied literally; the common rows agree by compatibility. -/
noncomputable def rows : Semantics K where
  E c d := table₀ c d.1
  orderly := table_orderly s D E w hD hE semD semE hc

theorem rows_left c d :
    (rows hD hE hc).E (l c) (leftBelow₀ c d) =
      semD.E c d :=
  (table_left s D E w hD hE semD semE c d.1).trans (total_below semD c d)

theorem rows_right c d :
    (rows hD hE hc).E (r c) (rightBelow s D E w hD hE c d) =
      semE.E c d :=
  (table_right s D E w hD hE semD semE hc c d.1).trans (total_below semE c d)

