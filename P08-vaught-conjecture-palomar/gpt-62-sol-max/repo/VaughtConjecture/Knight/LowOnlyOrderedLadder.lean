/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyRecursiveCharts
public import VaughtConjecture.Knight.WholeDonorBoundary

@[expose] public section

namespace VaughtConjecture.Knight.WholeDonorBoundary.Input

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)} {m n : ℕ}
  (I : Input A B C R m n n)

/-- The source family's root identifies the actual common boundary occurrences. -/
abbrev RootMatches (root : LowOnly.CommonRoot I.left I.right) :=
  ∀ i : Cell I.common.scheme, ∃ a : I.left.scheme.below (root.A, root.A.card),
    a.1 = I.shared.f i ∧ (root.face a).1 = I.shared.g i

end VaughtConjecture.Knight.WholeDonorBoundary.Input

namespace VaughtConjecture.Knight.LowOnlyOrderedLadder

open Transform Value ExtOrd AmalgamationPlan CappedDonor

open LowOnly RelativeLadderLayer

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : I.RootMatches F.root)

def field (d : Cell I.boundary) : Field I.left I.right :=
  match (OrderedFaceBoundary.enumeration I.leftScheme I.rightScheme I.shared).symm d with
  | .inl c => .inl c
  | .inr c => .inr (.inl c.1)

theorem field_read (S : State I.left I.right) (d : Cell I.boundary) :
    S.profile (field I d) = I.paste S.u S.v d := by
  unfold field WholeDonorBoundary.Input.paste OrderedFaceBoundarySemantics.paste Function.comp
  split <;> rename_i h <;> erw [h] <;> rfl

include hroot in
theorem shared {S : State I.left I.right} (hs : F.root.Shared S.u S.v)
    (i : Cell I.common.scheme) : S.u (I.shared.f i) = S.v (I.shared.g i) := by
  obtain ⟨a, ha, hb⟩ := hroot i
  exact ha ▸ hb ▸ hs a

include hroot in
theorem field_private {j : ℕ} {S : State I.left I.right} (hs : F.Admissible j S)
    (d : Cell I.right.scheme) : S.profile (field I (I.rightFace.map d)) = S.v d := by
  rw [field_read]
  exact I.paste_right S.u S.v (shared I F hroot hs.shared) d

/-- The boundary has no ambient-full owner; no global bound on retained grades
is imposed. -/
theorem proper (hB : B ⊂ A) (hC : C ⊂ A) (d : Cell I.boundary) : I.boundary.scope d ≠ A :=
  I.proper hB hC d

include hroot in
/-- Every admitted grade-one vector is lawful on the actual inherited boundary.
The proof uses its two original lawful restrictions and literal root equations. -/
theorem boundary_lawful {j : ℕ} (S : State I.left I.right) (hs : F.Admissible j S) :
    RespectsSemanticsBelow I.rows (A, j) (fun d => S.profile (field I d.1)) := by
  simp only [field_read]
  exact I.paste_respects_below hs.lawfulP hs.lawfulC (shared I F hroot hs.shared)
    grade_le_effC grade_le_effC

theorem field_donor (S : State I.left I.right) (d : Cell I.left.scheme) :
    S.profile (field I (I.leftFace.map d)) = S.u d :=
  (field_read I S (I.leftFace.map d)).trans (I.paste_left S.u S.v d)

end

end VaughtConjecture.Knight.LowOnlyOrderedLadder
