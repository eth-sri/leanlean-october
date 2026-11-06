/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.LowOnlyGradeOneLift
import VaughtConjecture.Knight.WholeDonorBoundary

/-! # Original-boundary premises for the LOW ladder are derived

The input is an actual ordered union of two legal cofaces, together with the
literal common-root occurrence correspondence used by the LOW family. Zero
padding is used only to prove inherited-boundary lawfulness; it does not change
the installed ladder rows or discard future fields from its catalogue.
-/

namespace VaughtConjecture.Knight.LowOnlyOrderedLadder
open    AmalgamationPlan CappedDonor
open LowOnly RelativeLadderLayer
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : F.root.Covers I.shared.f I.shared.g)

def field (d : Cell I.boundary) : Field I.left I.right :=
  match (OrderedFaceBoundary.enumeration I.shared).symm d with
  | .inl c => .inl c
  | .inr c => .inr (.inl c.1)

theorem field_read {S : State I.left I.right} {d : Cell I.boundary} :
    S.profile (field I d) = I.paste S.u S.v d := by
  
  change S.profile (match (OrderedFaceBoundary.enumeration I.shared).symm d with
    | .inl c => .inl c
    | .inr c => .inr (.inl c.1)) = ProfileFaceUnion.paste I.shared.g S.u S.v
      ((OrderedFaceBoundary.enumeration I.shared).symm d)
  cases (OrderedFaceBoundary.enumeration I.shared).symm d <;> rfl

include hroot in
theorem shared {S : State I.left I.right} (hs : F.root.Shared S.u S.v)
    i : S.u (I.shared.f i) = S.v (I.shared.g i) := by
  obtain ⟨a, ha, hb⟩ := hroot i
  exact ha ▸ hb ▸ hs a

include hroot in
variable {I F} in
theorem field_private {S : State I.left I.right} (hs : F.Admissible 1 S)
    (d : Cell I.right.scheme) : S.profile (field I (I.rightFace.map d)) = S.v d := by
  rw [field_read]
  exact I.paste_right S.u S.v (shared I F hroot hs.shared) d

variable {I} in
/-- The boundary has no ambient-full owner; no global bound on retained grades
is imposed. -/
theorem proper (hB : B ⊂ A) (hC : C ⊂ A) d : I.boundary.scope d ≠ A := by
  rcases OrderedFaceBoundaryRows.covered d with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · have hs := I.leftScheme.scope_subset d
    change I.boundary.scope (I.leftFace.map d) ≠ A
    rw [show I.boundary.scope (I.leftFace.map d) = I.leftScheme.scope d from
      congrArg Prod.fst (I.leftFace.index d)]
    exact fun he => hB.not_ge (he ▸ hs)
  · have hs := I.rightScheme.scope_subset d
    change I.boundary.scope (I.rightFace.map d) ≠ A
    rw [show I.boundary.scope (I.rightFace.map d) = I.rightScheme.scope d from
      congrArg Prod.fst (I.rightFace.index d)]
    exact fun he => hC.not_ge (he ▸ hs)

include hroot in
/-- Every admitted grade-one vector is lawful on the actual inherited boundary.
The proof uses its two original lawful restrictions and literal root equations. -/
theorem boundary_lawful (S : State I.left I.right) (hs : F.Admissible 1 S) :
    RespectsSemanticsBelow I.rows (A, 1) (fun d => S.profile (field I d.1)) := by
  have hn  := (Nat.succ_le_of_lt F.gap.K_pos).trans F.gap.K_le
  let u := CellScheme.zeroAbove (S.lowerP 1)
  let v := CellScheme.zeroAbove (S.lowerC 1)
  have hshared (i : Cell I.common.scheme) : u (I.shared.f i) = v (I.shared.g i) := by
    have hg : I.left.scheme.grade (I.shared.f i) = I.right.scheme.grade (I.shared.g i) :=
      congrArg (fun x => x.2) (I.shared.shared i)
    by_cases hd : I.left.scheme.grade (I.shared.f i) ≤ min 1 n
    · have he : I.right.scheme.grade (I.shared.g i) ≤ min 1 n := hg ▸ hd
      rw [show u (I.shared.f i) = S.u (I.shared.f i) from
        CellScheme.zeroAbove_low (S.lowerP 1) ⟨_, Finset.subset_univ _, hd⟩,
        show v (I.shared.g i) = S.v (I.shared.g i) from
        CellScheme.zeroAbove_low (S.lowerC 1) ⟨_, Finset.subset_univ _, he⟩]
      exact shared I F hroot hs.shared i
    · have he : ¬ I.right.scheme.grade (I.shared.g i) ≤ min 1 n := hg ▸ hd
      exact (CellScheme.zeroAbove_high hd).trans
        (CellScheme.zeroAbove_high he).symm
  have hl := (I.paste_respects hs.lawfulP.zeroAbove hs.lawfulC.zeroAbove hshared).toBelow (A, 1)
  have he : (fun d : I.boundary.below (A, 1) => S.profile (field I d.1)) =
      (fun d => I.paste u v d.1) := by
    funext d
    rw [field_read]
    rcases OrderedFaceBoundaryRows.covered d.1 with ⟨c, hc⟩ | ⟨c, hc⟩
    · have hg : I.left.scheme.grade c ≤ min 1 n := by
        have hi := d.2.2
        
        rw [← hc] at hi
        change I.boundary.grade (I.leftFace.map c) ≤ 1 at hi
        have hgrade := congrArg Prod.snd (I.leftFace.index c)
        change I.boundary.grade (I.leftFace.map c) = I.left.scheme.grade c at hgrade
        rw [hgrade] at hi
        simpa only [min_eq_left hn] using hi
      rw [← hc]
      
      exact (I.paste_left S.u S.v c).trans
        ((CellScheme.zeroAbove_low (S.lowerP 1) ⟨c, Finset.subset_univ _, hg⟩).symm.trans
          (I.paste_left u v c).symm)
    · have hg : I.right.scheme.grade c ≤ min 1 n := by
        have hi := d.2.2
        
        rw [← hc] at hi
        change I.boundary.grade (I.rightFace.map c) ≤ 1 at hi
        have hgrade := congrArg Prod.snd (I.rightFace.index c)
        change I.boundary.grade (I.rightFace.map c) = I.right.scheme.grade c at hgrade
        rw [hgrade] at hi
        simpa only [min_eq_left hn] using hi
      rw [← hc]
      
      exact (I.paste_right S.u S.v (shared I F hroot hs.shared) c).trans
        ((CellScheme.zeroAbove_low (S.lowerC 1) ⟨c, Finset.subset_univ _, hg⟩).symm.trans
          (I.paste_right u v hshared c).symm)
  exact he ▸ hl

def privateIncl (d : I.right.scheme.below (effC n 1)) : I.boundary.below (A, 1) :=
  ⟨I.rightFace.map d.1,
    I.boundary.scope_subset _, by
      have hg := congrArg Prod.snd (I.rightFace.index d.1)
      change I.boundary.grade (I.rightFace.map d.1) = I.right.scheme.grade d.1 at hg
      exact hg.le.trans (d.2.2.trans (min_le_left _ _))⟩

include hroot in
/-- A complete positive-cap physical lift on the actual ordered two-face ladder.
All semantic producer premises of `private_positive_lift` are discharged here.
The remaining inputs are the legal cofaces, their literal root correspondence,
proper placement, and the arbitrary lawful query. -/
def private_positive_lift (hA : 0 < A.card) (hB : B ⊂ A) (hC : C ⊂ A)
    {p}
    {q : (RelativeLadderLayer.carrier I.boundary hA
      (X := Field I.left I.right) (Q := F.Anchor 1)).below (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (effC n 1) p)
    (hq : RespectsSemanticsBelow
      (rows I.boundary I.rows hA (field I) (F.fields 1) (proper hB hC)) (A, 1) q)
    {γ} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (q (Family.privateAt F I.boundary hA (privateIncl I) d)) γ = min (p d) γ) :=
  Family.private_positive_lift F I.boundary I.rows hA (field I) (proper hB hC)
    (boundary_lawful I F hroot) (privateIncl I)
    (fun _ hs d => field_private hroot hs d.1) hp hq hγ hpos hag

