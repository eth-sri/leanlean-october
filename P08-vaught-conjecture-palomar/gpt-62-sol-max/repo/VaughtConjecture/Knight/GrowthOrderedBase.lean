/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthScalarLedger
public import VaughtConjecture.Knight.WholeDonorBoundary
public import VaughtConjecture.Knight.CommonFaceAlignment
public import VaughtConjecture.Knight.RelativeLadderRankRendering

@[expose] public section

namespace VaughtConjecture.Knight.WholeDonorBoundary.Input

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)} {m n J : ℕ}
  (I : Input A B C R m (n + 1) J)

abbrev GrowthData := RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows

/-- The relative-data root on the boundary's actual common face. -/
abbrev GrowthAttachment (X : I.GrowthData) :=
  Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X

end VaughtConjecture.Knight.WholeDonorBoundary.Input

namespace VaughtConjecture.Knight.GrowthOrderedBase

open Transform Value ExtOrd AmalgamationPlan Growth RelativeLadderLayer SemSchemeBoundaryInput

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)

def field (d : Cell I.boundary) : Field I.right.scheme I.left.scheme :=
  match (OrderedFaceBoundary.enumeration I.leftScheme I.rightScheme I.shared).symm d with
  | .inl c => .inr c
  | .inr c => .inl c.1

theorem field_read (S : State I.right.scheme I.left.scheme) (d : Cell I.boundary) :
    S.profile (field I d) = I.paste S.donorValues S.privateValues d := by
  unfold field WholeDonorBoundary.Input.paste OrderedFaceBoundarySemantics.paste Function.comp
  split <;> rename_i h <;> erw [h] <;> rfl

include T in
theorem shared {j : ℕ} {S : State I.right.scheme I.left.scheme} (hs : Admitted X j S)
    (d : Cell I.common.scheme) :
    S.donorValues (I.shared.f d) = S.privateValues (I.shared.g d) := by
  let a := faceBelow I.left I.common I.commonLeft I.visibleLeft I.faceLeft d
  have ha : a.1 = I.shared.f d := faceBelow_val _ _ _ _ _ _
  have hb : (rootMap I.common I.commonLeft I.visibleLeft I.faceLeft
      I.commonRight I.visibleRight I.faceRight m a).1 = I.shared.g d := by
    rw [rootMap, commonFace_faceBelow]
    exact faceBelow_val _ _ _ _ _ _
  have h := hs.shared (T.full a)
  change S.donorValues a.1 = S.privateValues (X.κ (T.full a)).1 at h
  simp_all [← T.at_occurrence a, ha, hb]

theorem field_donor (S : State I.right.scheme I.left.scheme) (d : Cell I.left.scheme) :
    S.profile (field I (I.leftFace.map d)) = S.donorValues d :=
  (field_read I S _).trans (I.paste_left _ _ d)

include T in
theorem field_private {j : ℕ} {S : State I.right.scheme I.left.scheme}
    (hs : Admitted X j S) (d : Cell I.right.scheme) :
    S.profile (field I (I.rightFace.map d)) = S.privateValues d :=
  (field_read I S _).trans (I.paste_right _ _ (shared I X T hs) d)

theorem proper (hB : B ⊂ A) (hC : C ⊂ A) (d : Cell I.boundary) :
    I.boundary.scope d ≠ A :=
  I.proper hB hC d

include T in
theorem boundary_lawful {j : ℕ} {S : State I.right.scheme I.left.scheme} (hs : Admitted X j S) :
    RespectsSemanticsBelow I.rows (A, j) (fun d => S.profile (field I d.1)) := by
  simp only [field_read]
  exact I.paste_respects_below hs.donor_lawful hs.private_lawful (shared I X T hs)
    (fun _ => Iff.rfl) (fun _ => Iff.rfl)

instance : Fintype (Catalogue X 1) := Fintype.ofFinite _

include T in
theorem anchor_lawful (a : Catalogue X 1) :
    RespectsSemanticsBelow I.rows (A, 1) (fun d => a.val (field I d.1)) := by
  obtain ⟨S, hs, he⟩ := a.property.2
  rw [← he]
  exact boundary_lawful I X T hs

end

end VaughtConjecture.Knight.GrowthOrderedBase
