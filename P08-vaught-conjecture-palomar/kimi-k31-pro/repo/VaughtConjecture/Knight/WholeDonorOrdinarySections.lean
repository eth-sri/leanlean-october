/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.WholeDonorBoundary
public import VaughtConjecture.Knight.CanonicalRecursiveLiteralRows
public import VaughtConjecture.Knight.OrbitSupportSubstitution

/-! # Ordinary selected sections over two literal input faces

This is the first scope step for new31, independent of LOW/HIGH catalogues.
The original schemes supply consistency and lawful input sections. The ordinary
grade recursion constructs the output rows and all selected-section receipts.
One fixed external grid and ceiling are used, and support is stated over the two
original occurrence vectors, not over unidentified intermediate coordinates.

This module does not fill missing proper mixed scopes. Inherited-target lifting
is transported, but full mixed-target lifting still needs the scope induction.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.WholeDonorOrdinarySections
open AmalgamationPlan Transform Value ExtOrd SourcePrefixRows OrbitPrefixSupport
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)}
variable {m nL nR : ℕ} (I : WholeDonorBoundary.Input A B C R m nL nR)

theorem covered (d : Cell I.boundary) :
    (∃ c, I.leftFace.map c = d) ∨ ∃ c, I.rightFace.map c = d :=
  OrderedFaceBoundaryRows.covered I.leftScheme I.rightScheme I.shared
    R I.isPlan I.leftPlan_le I.rightPlan_le d

theorem paste_bound {p : Cell I.left.scheme → ExtOrd} {q : Cell I.right.scheme → ExtOrd}
    {θ : ExtOrd} (hp : ∀ d, p d ≤ θ) (hq : ∀ d, q d ≤ θ)
    (hroot : ∀ i, p (I.shared.f i) = q (I.shared.g i)) :
    ∀ d, I.paste p q d ≤ θ := by
  intro d
  rcases covered I d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact (I.paste_left p q c) ▸ hp c
  · exact (I.paste_right p q hroot c) ▸ hq c

theorem paste_agreement {p p' : Cell I.left.scheme → ExtOrd}
    {q q' : Cell I.right.scheme → ExtOrd} {h : ExtOrd}
    (hr : ∀ i, p (I.shared.f i) = q (I.shared.g i))
    (hr' : ∀ i, p' (I.shared.f i) = q' (I.shared.g i))
    (hp : Agree p p' h) (hq : Agree q q' h) : Agree (I.paste p q) (I.paste p' q') h := by
  intro d
  rcases covered I d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact (congrArg (fun v => min v h) (I.paste_left p q c)).trans
      ((hp c).trans (congrArg (fun v => min v h) (I.paste_left p' q' c)).symm)
  · exact (congrArg (fun v => min v h) (I.paste_right p q hr c)).trans
      ((hq c).trans (congrArg (fun v => min v h) (I.paste_right p' q' hr' c)).symm)

variable (hBA : B ≠ A) (hCA : C ≠ A)

include hBA hCA in
theorem proper_boundary (d : Cell I.boundary) : I.boundary.scope d ≠ A := by
  rcases covered I d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · intro he
    have hc := I.leftScheme.isPlan.subset_of_mem (I.leftScheme.scope_mem_plan c)
    change (I.leftScheme.cell c).1 ⊆ B at hc
    rw [← I.leftFace.index c] at hc
    change I.boundary.scope (I.leftFace.map c) ⊆ B at hc
    rw [he] at hc
    exact hBA (Finset.Subset.antisymm
      (I.isPlan.subset_of_mem (I.leftPlan_le I.leftScheme.isPlan.domain_mem)) hc)
  · intro he
    have hc := I.rightScheme.isPlan.subset_of_mem (I.rightScheme.scope_mem_plan c)
    change (I.rightScheme.cell c).1 ⊆ C at hc
    rw [← I.rightFace.index c] at hc
    change I.boundary.scope (I.rightFace.map c) ⊆ C at hc
    rw [he] at hc
    exact hCA (Finset.Subset.antisymm
      (I.isPlan.subset_of_mem (I.rightPlan_le I.rightScheme.isPlan.domain_mem)) hc)

variable (n : ℕ) (hA : n + 3 ≤ A.card)

abbrev carrier := CanonicalRecursiveContract.carrier I.rows n hA
abbrev original := CanonicalRecursiveContract.boundary I.rows n hA
abbrev rows := CanonicalRecursiveSemantics.rows I.rows (proper_boundary I hBA hCA) n hA

theorem consistent : (rows I hBA hCA n hA).IsConsistent :=
  CanonicalRecursiveSemantics.consistent I.rows (proper_boundary I hBA hCA) I.consistent n hA

variable {p : Cell I.left.scheme → ExtOrd} {q : Cell I.right.scheme → ExtOrd}
variable (hp : RespectsSemantics I.left.rows p) (hq : RespectsSemantics I.right.rows q)
variable (hr : ∀ i, p (I.shared.f i) = q (I.shared.g i))
variable (htp : ∀ d, p d ≠ ⊤) (htq : ∀ d, q d ≠ ⊤)

variable {G : Finset ExtOrd} {θ : ExtOrd}
variable (hG : ∀ z ∈ G, SelfVis (n + 3) z) (hθ : SelfVis (n + 3) θ)

end
end VaughtConjecture.Knight.WholeDonorOrdinarySections
