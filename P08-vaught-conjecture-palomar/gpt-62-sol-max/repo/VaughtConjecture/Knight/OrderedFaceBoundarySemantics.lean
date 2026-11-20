/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrderedFaceBoundaryRows
public import VaughtConjecture.Knight.ExactSemanticFace

@[expose] public section

namespace VaughtConjecture.Knight.OrderedFaceBoundarySemantics

open AmalgamationPlan OrderedFaceBoundary OrderedFaceBoundaryRows

open AmalgamatedBoundary (Overlap)

open Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}

variable (D : CellScheme B) (E : CellScheme C)

variable {k : ℕ} (w : Overlap D E k)

variable (R : Finset (Finset ι)) (hR : Plan.IsPlan A R)

variable (hD : D.plan ⊆ R) (hE : E.plan ⊆ R)

variable (semD : Semantics D) (semE : Semantics E)

variable (hc : Compatible D E w semD semE)

local notation "K" => scheme D E w R hR hD hE

local notation "l" => leftCell D E w R hR hD hE

local notation "r" => rightCell D E w R hR hD hE

local notation "U" => patches D E w R hR hD hE

local notation "sem" => rows D E w R hR hD hE semD semE

noncomputable def leftFace : ExactSemanticFace semD sem where
  map := ⟨l, (left_order D E w R hR hD hE).injective⟩
  index := left_index D E w R hR hD hE
  exhaustive := left_exhaustive D E w R hR hD hE
  row := (U).old_row semD semE

noncomputable def rightFace : ExactSemanticFace semE sem where
  map := ⟨r, (right_order D E w R hR hD hE).injective⟩
  index := right_index D E w R hR hD hE
  exhaustive := right_exhaustive D E w R hR hD hE
  row := (U).low_row semD semE (agreement D E w R hR hD hE semD semE hc)

include hc in
theorem consistent (hd : semD.IsConsistent) (he : semE.IsConsistent) : (sem).IsConsistent :=
  (U).consistent semD semE (agreement D E w R hR hD hE semD semE hc) hd he

theorem coded (hd : semD.IsCoded) (he : semE.IsCoded) : (sem).IsCoded := (U).coded semD semE hd he

include hc in
/-- There are no additional cross-face lawfulness conditions on the proper boundary. -/
theorem respects_iff (p : Cell K → ExtOrd) : RespectsSemantics sem p ↔
    RespectsSemantics semD (p ∘ l) ∧ RespectsSemantics semE (p ∘ r) :=
  ⟨fun hp => ⟨(leftFace D E w R hR hD hE semD semE).restrict hp,
    (rightFace D E w R hR hD hE semD semE hc).restrict hp⟩,
    fun ⟨hp, hq⟩ => (U).respects semD semE (agreement D E w R hR hD hE semD semE hc) hp hq⟩

noncomputable def paste (p : Cell D → ExtOrd) (q : Cell E → ExtOrd) : Cell K → ExtOrd :=
  ProfileFaceUnion.paste w.g p q ∘ (enumeration D E w).symm

theorem paste_left (p : Cell D → ExtOrd) (q : Cell E → ExtOrd) (d : Cell D) :
    paste D E w R hR hD hE p q (l d) = p d := by
  change ProfileFaceUnion.paste w.g p q ((enumeration D E w).symm
    (enumeration D E w (ProfileFaceUnion.left w.g d))) = p d
  rw [Equiv.symm_apply_apply]
  rfl

theorem paste_right (p : Cell D → ExtOrd) (q : Cell E → ExtOrd)
    (h : ∀ i, p (w.f i) = q (w.g i)) (e : Cell E) :
    paste D E w R hR hD hE p q (r e) = q e := by
  change ProfileFaceUnion.paste w.g p q ((enumeration D E w).symm
    (enumeration D E w (ProfileFaceUnion.right w.f w.g e))) = q e
  rw [Equiv.symm_apply_apply]
  exact ProfileFaceUnion.paste_right w.f w.g h e

end VaughtConjecture.Knight.OrderedFaceBoundarySemantics
