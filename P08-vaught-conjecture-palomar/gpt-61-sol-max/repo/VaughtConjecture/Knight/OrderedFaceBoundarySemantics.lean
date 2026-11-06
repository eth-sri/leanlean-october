/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.OrderedFaceBoundaryRows
import VaughtConjecture.Knight.ExactSemanticFace

/-! # Lawful pasting on two arbitrary exact ordered faces

Generalizes `AmalgamatedBoundarySemantics` beyond coatom geometry.
The constructed inherited boundary is coded and consistent when both inputs are.
A boundary labelling is lawful exactly when both literal face restrictions are.
Compatible lawful inputs therefore have a unique lawful boundary paste.

No completeness or lifting at new mixed indices is asserted. The boundary has no
new owners; it is not packaged as a legal receiving scheme.
-/

namespace VaughtConjecture.Knight.OrderedFaceBoundarySemantics

open AmalgamationPlan OrderedFaceBoundary OrderedFaceBoundaryRows
open AmalgamatedBoundary (Overlap)
open  Value 

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
variable (D : CellScheme B) (E : CellScheme C)
variable {k : ℕ} (w : Overlap D E k)
variable (R : VaughtConjecture.AmalgamationPlan.SupportFamily ι) (hR : Plan.IsPlan A R)
variable (hD : D.plan ⊆ R) (hE : E.plan ⊆ R)
variable (semD : Semantics D) (semE : Semantics E)
variable (hc : Compatible D E w semD semE)

local notation "K" => scheme D E w R hR hD hE
local notation "l" => leftCell D E w R hR hD hE
local notation "r" => rightCell D E w R hR hD hE
local notation "sem" => rows D E w R hR hD hE semD semE hc

variable {D E w R semD semE} in
noncomputable def leftFace : ExactSemanticFace semD sem where
  map := ⟨l, (left_order).injective⟩
  index := left_index D E w R hR hD hE
  exhaustive := left_exhaustive D E w R hR hD hE
  row := rows_left D E w R hR hD hE semD semE hc

variable {D E w R semD semE} in
noncomputable def rightFace : ExactSemanticFace semE sem where
  map := ⟨r, (right_order).injective⟩
  index := right_index D E w R hR hD hE
  exhaustive := right_exhaustive D E w R hR hD hE
  row := rows_right D E w R hR hD hE semD semE hc

theorem consistent (hd : semD.IsConsistent) (he : semE.IsConsistent) : (sem).IsConsistent := by
  intro c
  rcases covered c with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact (leftFace hR hD hE hc).consistent_at hd c
  · exact (rightFace hR hD hE hc).consistent_at he c

theorem coded (hd : semD.IsCoded) (he : semE.IsCoded) : (sem).IsCoded := by
  intro c d
  rcases covered c with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact (leftFace hR hD hE hc).coded_at hd c d
  · exact (rightFace hR hD hE hc).coded_at he c d

/-- There are no additional cross-face lawfulness conditions on the proper
boundary: every locality and availability target is inherited. -/
theorem respects_iff p : RespectsSemantics sem p ↔
    RespectsSemantics semD (p ∘ l) ∧ RespectsSemantics semE (p ∘ r) := by 
  let core1 := rightFace hR hD hE hc
  let core2 := leftFace hR hD hE hc
  let core3 (c : Cell K) := covered c
  constructor
  · intro hp
    exact ⟨core2.restrict hp,
      core1.restrict hp⟩
  · rintro ⟨hpD, hpE⟩
    constructor
    · intro c
      rcases core3 c with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · change p (l c) = extVisibilityReplace (p (l c))
          ((K).cell (l c)).2 ((K).cell (l c)).2
        rw [left_index]
        exact hpD.orderly c
      · change p (r c) = extVisibilityReplace (p (r c))
          ((K).cell (r c)).2 ((K).cell (r c)).2
        rw [right_index]
        exact hpE.orderly c
    · intro c
      rcases core3 c with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · exact core2.locality_of_restrict hpD c
      · exact core1.locality_of_restrict hpE c
    · intro c e hs hg
      rcases core3 e with ⟨e, rfl⟩ | ⟨e, rfl⟩
      · exact core2.availability_at hpD c e hs hg
      · exact core1.availability_at hpE c e hs hg

local notation "enumeration₀" => enumeration w

noncomputable def paste (p : CellLabels D) (q : CellLabels E) : CellLabels K :=
  ProfileFaceUnion.paste w.g p q ∘ (enumeration₀).symm

theorem paste_left p q d :
    paste D E w R hR hD hE p q (l d) = p d := by
  change ProfileFaceUnion.paste w.g p q ((enumeration₀).symm
    (enumeration₀ (ProfileFaceUnion.left d))) = p d
  rw [Equiv.symm_apply_apply]
  rfl

theorem paste_right p q
    (h : ∀ i, p (w.f i) = q (w.g i)) e :
    paste D E w R hR hD hE p q (r e) = q e := by
  change ProfileFaceUnion.paste w.g p q ((enumeration₀).symm
    (enumeration₀ (ProfileFaceUnion.right w.f w.g e))) = q e
  rw [Equiv.symm_apply_apply]
  exact ProfileFaceUnion.paste_right h e

