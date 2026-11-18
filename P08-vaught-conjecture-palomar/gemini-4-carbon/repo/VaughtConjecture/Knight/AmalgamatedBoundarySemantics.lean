/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.AmalgamatedBoundaryRows
public import VaughtConjecture.Knight.ExactSemanticFace

/-! # Semantic assembly and lawful pasting on ordered boundaries -/

@[expose] public section

namespace VaughtConjecture.Knight.OrderedFaceBoundarySemantics
open AmalgamationPlan OrderedFaceBoundary OrderedFaceBoundaryRows
open AmalgamatedBoundary (Overlap)
open Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
variable (D : CellScheme B) (E : CellScheme C) {k : ℕ} (w : Overlap D E k)
variable (R : Finset (Finset ι)) (hR : Plan.IsPlan A R)
variable (hD : D.plan ⊆ R) (hE : E.plan ⊆ R)
variable (semD : Semantics D) (semE : Semantics E) (hc : Compatible D E w semD semE)

local notation "K" => scheme D E w R hR hD hE
local notation "l" => leftCell D E w R hR hD hE
local notation "r" => rightCell D E w R hR hD hE
local notation "sem" => rows D E w R hR hD hE semD semE hc

noncomputable def leftFace : ExactSemanticFace semD sem where
  map := ⟨l, (left_order D E w R hR hD hE).injective⟩
  index := left_index D E w R hR hD hE
  exhaustive := left_exhaustive D E w R hR hD hE
  row := rows_left D E w R hR hD hE semD semE hc

noncomputable def rightFace : ExactSemanticFace semE sem where
  map := ⟨r, (right_order D E w R hR hD hE).injective⟩
  index := right_index D E w R hR hD hE
  exhaustive := right_exhaustive D E w R hR hD hE
  row := rows_right D E w R hR hD hE semD semE hc

theorem consistent (hd : semD.IsConsistent) (he : semE.IsConsistent) : (sem).IsConsistent := by
  intro c
  rcases covered D E w R hR hD hE c with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact (leftFace D E w R hR hD hE semD semE hc).consistent_at hd c
  · exact (rightFace D E w R hR hD hE semD semE hc).consistent_at he c

theorem coded (hd : semD.IsCoded) (he : semE.IsCoded) : (sem).IsCoded := by
  intro c d
  rcases covered D E w R hR hD hE c with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact (leftFace D E w R hR hD hE semD semE hc).coded_at hd c d
  · exact (rightFace D E w R hR hD hE semD semE hc).coded_at he c d

theorem respects_iff (p : Cell K → ExtOrd) : RespectsSemantics sem p ↔
    RespectsSemantics semD (p ∘ l) ∧ RespectsSemantics semE (p ∘ r) := by
  constructor
  · intro hp
    exact ⟨(leftFace D E w R hR hD hE semD semE hc).restrict hp,
      (rightFace D E w R hR hD hE semD semE hc).restrict hp⟩
  · rintro ⟨hpD, hpE⟩
    refine ⟨fun c => ?_, fun c => ?_, fun c e hs hg => ?_⟩
    · rcases covered D E w R hR hD hE c with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · change p (l c) = extVisibilityReplace (p (l c)) ((K).cell (l c)).2 ((K).cell (l c)).2
        rw [left_index]; exact hpD.orderly c
      · change p (r c) = extVisibilityReplace (p (r c)) ((K).cell (r c)).2 ((K).cell (r c)).2
        rw [right_index]; exact hpE.orderly c
    · rcases covered D E w R hR hD hE c with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · exact (leftFace D E w R hR hD hE semD semE hc).locality_of_restrict hpD c
      · exact (rightFace D E w R hR hD hE semD semE hc).locality_of_restrict hpE c
    · rcases covered D E w R hR hD hE e with ⟨e, rfl⟩ | ⟨e, rfl⟩
      · exact (leftFace D E w R hR hD hE semD semE hc).availability_at hpD c e hs hg
      · exact (rightFace D E w R hR hD hE semD semE hc).availability_at hpE c e hs hg

noncomputable def paste (p : Cell D → ExtOrd) (q : Cell E → ExtOrd) : Cell K → ExtOrd :=
  ProfileFaceUnion.paste w.g p q ∘ (enumeration D E w).symm

theorem paste_left (p : Cell D → ExtOrd) (q : Cell E → ExtOrd) (d : Cell D) :
    paste D E w R hR hD hE p q (l d) = p d := by
  change ProfileFaceUnion.paste w.g p q
    ((enumeration D E w).symm (enumeration D E w (ProfileFaceUnion.left w.g d))) = p d
  rw [Equiv.symm_apply_apply]; rfl

theorem paste_right (p : Cell D → ExtOrd) (q : Cell E → ExtOrd)
    (h : ∀ i, p (w.f i) = q (w.g i)) (e : Cell E) :
    paste D E w R hR hD hE p q (r e) = q e := by
  change ProfileFaceUnion.paste w.g p q
    ((enumeration D E w).symm (enumeration D E w (ProfileFaceUnion.right w.f w.g e))) = q e
  rw [Equiv.symm_apply_apply]
  exact ProfileFaceUnion.paste_right w.f w.g h e

theorem paste_respects {p : Cell D → ExtOrd} {q : Cell E → ExtOrd}
    (hp : RespectsSemantics semD p) (hq : RespectsSemantics semE q)
    (h : ∀ i, p (w.f i) = q (w.g i)) :
    RespectsSemantics sem (paste D E w R hR hD hE p q) :=
  (respects_iff D E w R hR hD hE semD semE hc _).mpr
    ⟨by simpa only [Function.comp_def, paste_left] using hp,
     by simpa only [Function.comp_def, paste_right D E w R hR hD hE p q h] using hq⟩

theorem section_iff {p : Cell D → ExtOrd} {q : Cell E → ExtOrd}
    (hp : RespectsSemantics semD p) (hq : RespectsSemantics semE q) :
    (∃ t, RespectsSemantics sem t ∧ (∀ d, t (l d) = p d) ∧ ∀ e, t (r e) = q e) ↔
      ∀ i, p (w.f i) = q (w.g i) := by
  constructor
  · rintro ⟨t, _, hl, hr⟩ i
    exact (hl _).symm.trans ((congrArg t (shared_cell D E w R hR hD hE i)).trans (hr _))
  · intro h
    exact ⟨paste D E w R hR hD hE p q,
      paste_respects D E w R hR hD hE semD semE hc hp hq h,
      paste_left D E w R hR hD hE p q, paste_right D E w R hR hD hE p q h⟩

end VaughtConjecture.Knight.OrderedFaceBoundarySemantics

namespace VaughtConjecture.Knight.AmalgamatedBoundarySemantics
open AmalgamationPlan AmalgamatedBoundaryPlan AmalgamatedBoundary AmalgamatedBoundaryRows
open Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} (s : Step A)
variable (D : CellScheme (A.erase s.a)) (E : CellScheme (A.erase s.b))
variable {k : ℕ} (w : Overlap D E k) (hD : D.plan = s.left) (hE : E.plan = s.right)
variable (semD : Semantics D) (semE : Semantics E) (hc : Compatible s D E w semD semE)

local notation "K" => scheme s D E w hD hE
local notation "l" => leftCell s D E w hD hE
local notation "r" => rightCell s D E w hD hE
local notation "sem" => rows s D E w hD hE semD semE hc

@[reducible] noncomputable def leftFace : ExactSemanticFace semD sem :=
  OrderedFaceBoundarySemantics.leftFace D E w s.plan (isPlan s)
    (left_sub s D hD) (right_sub s E hE) semD semE hc

@[reducible] noncomputable def rightFace : ExactSemanticFace semE sem :=
  OrderedFaceBoundarySemantics.rightFace D E w s.plan (isPlan s)
    (left_sub s D hD) (right_sub s E hE) semD semE hc

theorem consistent (hd : semD.IsConsistent) (he : semE.IsConsistent) : (sem).IsConsistent :=
  OrderedFaceBoundarySemantics.consistent D E w s.plan (isPlan s)
    (left_sub s D hD) (right_sub s E hE) semD semE hc hd he

theorem coded (hd : semD.IsCoded) (he : semE.IsCoded) : (sem).IsCoded :=
  OrderedFaceBoundarySemantics.coded D E w s.plan (isPlan s)
    (left_sub s D hD) (right_sub s E hE) semD semE hc hd he



theorem section_iff {p : Cell D → ExtOrd} {q : Cell E → ExtOrd}
    (hp : RespectsSemantics semD p) (hq : RespectsSemantics semE q) :
    (∃ t, RespectsSemantics sem t ∧ (∀ d, t (l d) = p d) ∧ ∀ e, t (r e) = q e) ↔
      ∀ i, p (w.f i) = q (w.g i) :=
  OrderedFaceBoundarySemantics.section_iff D E w s.plan (isPlan s)
    (left_sub s D hD) (right_sub s E hE) semD semE hc hp hq

theorem proper_lift (hd : semD.IsBountiful) (he : semE.IsBountiful)
    {CI BJ : Finset ι × ℕ} (hCI : CI ∈ Plan.gradedPlan (K).plan)
    (hBJ : BJ ∈ Plan.gradedPlan (K).plan) (h : GradedLe CI BJ) (hne : CI ≠ BJ)
    (hB : BJ.1 ≠ A) (p : (K).below CI → ExtOrd) (q : (K).below BJ → ExtOrd) (γ : ExtOrd)
    (hp : RespectsSemanticsBelow sem CI p) (hq : RespectsSemanticsBelow sem BJ q)
    (hγ : extVisibilityReplace γ BJ.2 BJ.2 = γ)
    (ha : ∀ d, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ q', RespectsSemanticsBelow sem BJ q' ∧
      (∀ d, min (q' d) γ = min (q d) γ) ∧
      ∀ d, q' (CellScheme.below.mono h d) = p d := by
  rcases proper_pair_cover s hCI hBJ h hB with hleft | hright
  · have hbs := s.left_plan.subset_of_mem (Plan.mem_gradedPlan.mp hleft.2).1
    rw [← hD] at hleft
    exact (leftFace s D E w hD hE semD semE hc).lift hbs hleft.1 hleft.2 h hne hd
      p q γ hp hq hγ ha
  · have hbs := s.right_plan.subset_of_mem (Plan.mem_gradedPlan.mp hright.2).1
    rw [← hE] at hright
    exact (rightFace s D E w hD hE semD semE hc).lift hbs hright.1 hright.2 h hne he
      p q γ hp hq hγ ha

end VaughtConjecture.Knight.AmalgamatedBoundarySemantics
