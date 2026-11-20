/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrderedFaceBoundary
public import VaughtConjecture.Knight.FullScopeBountiful
public import VaughtConjecture.Knight.SemanticPatch

@[expose] public section

namespace VaughtConjecture.Knight.AmalgamatedBoundaryRows

open AmalgamationPlan

open Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι]

open Classical in
/-- Extend a semantic row by bottom outside its actual lower domain. -/
noncomputable def total {B : Finset ι} {D : CellScheme B} (sem : Semantics D)
    (c d : Cell D) : ExtOrd :=
  if h : GradedLe (D.cell d) (D.cell c) then sem.E c ⟨d, h⟩ else ⊥

theorem total_below {B : Finset ι} {D : CellScheme B} (sem : Semantics D)
    (c : Cell D) (d : D.below (D.cell c)) : total sem c d.1 = sem.E c d := by
  rw [total, dite_eq_left d.2]
  aesop

theorem total_outside {B : Finset ι} {D : CellScheme B} (sem : Semantics D)
    (c d : Cell D) (h : ¬ GradedLe (D.cell d) (D.cell c)) : total sem c d = ⊥ := by simp_all [total]

end VaughtConjecture.Knight.AmalgamatedBoundaryRows

namespace VaughtConjecture.Knight.OrderedFaceBoundaryRows

open AmalgamationPlan OrderedFaceBoundary Transform Value ExtOrd

open AmalgamatedBoundary (Overlap)

open AmalgamatedBoundaryRows (total total_below)

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}

variable (D : CellScheme B) (E : CellScheme C)

variable {k : ℕ} (w : Overlap D E k)

variable (R : Finset (Finset ι)) (hR : Plan.IsPlan A R)

variable (hD : D.plan ⊆ R) (hE : E.plan ⊆ R)

variable (semD : Semantics D) (semE : Semantics E)

local notation "K" => scheme D E w R hR hD hE

local notation "l" => leftCell D E w R hR hD hE

local notation "r" => rightCell D E w R hR hD hE

/-- Source equality on all shared occurrences, including every auxiliary. -/
def Compatible : Prop :=
  ∀ i j, total semD (w.f i) (w.f j) = total semE (w.g i) (w.g j)

theorem shared_cell (i : Fin k) : l (w.f i) = r (w.g i) :=
  (overlap D E w R hR hD hE _ _).mpr ⟨i, rfl, rfl⟩

theorem covered (c : Cell K) : (∃ d, l d = c) ∨ ∃ e, r e = c := by
  rcases ProfileFaceUnion.covered w.f w.g ((enumeration D E w).symm c) with
    ⟨d, hd⟩ | ⟨e, he⟩
  · exact Or.inl ⟨d, (congrArg (enumeration D E w) hd).trans
      ((enumeration D E w).apply_symm_apply c)⟩
  · exact Or.inr ⟨e, (congrArg (enumeration D E w) he).trans
      ((enumeration D E w).apply_symm_apply c)⟩

noncomputable def patches : SemanticPatchUnion D E K where
  old := ⟨⟨l, (left_order D E w R hR hD hE).injective⟩, left_index D E w R hR hD hE,
    fun c d hd => left_exhaustive D E w R hR hD hE d (hd.1.trans (D.scope_subset c))⟩
  low := ⟨⟨r, (right_order D E w R hR hD hE).injective⟩, right_index D E w R hR hD hE,
    fun c d hd => right_exhaustive D E w R hR hD hE d (hd.1.trans (E.scope_subset c))⟩
  cover := covered D E w R hR hD hE

local notation "U" => patches D E w R hR hD hE

theorem agreement (hc : Compatible D E w semD semE) : (U).Agreement semD semE := by
  apply (U).agreement_of_shared semD semE w.f w.g (shared_cell D E w R hR hD hE)
    (fun h => (overlap D E w R hR hD hE _ _).mp h)
  · intro i d
    exact w.left_exhaustive d.1 ((d.2.1.trans (subset_of_eq (congrArg Prod.fst (w.shared i)))).trans
      (E.scope_subset (w.g i)))
  · intro i j hd
    exact (total_below semD _ ⟨_, hd⟩).symm.trans ((hc i j).trans
      (total_below semE _ ⟨w.g j, by simpa only [← w.shared] using hd⟩))

/-- Both rows are copied literally; the common rows agree by compatibility. -/
noncomputable abbrev rows := (U).rows semD semE

end VaughtConjecture.Knight.OrderedFaceBoundaryRows
